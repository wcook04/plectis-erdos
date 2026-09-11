import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyEightATFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyEightATFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyEightATFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyEightATFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyEightATFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyEightATFastPow a n * fortyEightATFastPow a n * a
        else fortyEightATFastPow a n * fortyEightATFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyEightAT_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyEightAT_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyEightAT_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyEightAT_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyEightAT_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyEightAT_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyEightAT_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyEightAT_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyEightAT_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyEightAT_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyEightAT_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyEightAT_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyEightAT_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyEightAT_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyEightAT_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyEightAT_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyEightAT_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyEightAT_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyEightAT_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyEightAT_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyEightAT_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyEightAT_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyEightAT_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyEightAT_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyEightAT_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyEightAT_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyEightAT_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyEightAT_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyEightAT_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyEightAT_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyEightAT_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyEightAT_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyEightAT_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyEightAT_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyEightAT_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyEightAT_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyEightAT_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyEightAT_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyEightAT_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyEightAT_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyEightAT_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyEightAT_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyEightAT_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortyEightAT_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyEightAT_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyEightAT_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyEightAT_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyEightAT_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyEightAT_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyEightAT_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyEightAT_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyEightAT_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortyEightAT_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyEightAT_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyEightAT_281 : Nat.Prime 281 := by norm_num
private theorem prime_fortyEightAT_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyEightAT_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyEightAT_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyEightAT_311 : Nat.Prime 311 := by norm_num
private theorem prime_fortyEightAT_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyEightAT_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyEightAT_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyEightAT_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyEightAT_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyEightAT_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyEightAT_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyEightAT_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyEightAT_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyEightAT_389 : Nat.Prime 389 := by norm_num
private theorem prime_fortyEightAT_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyEightAT_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortyEightAT_409 : Nat.Prime 409 := by norm_num
private theorem prime_fortyEightAT_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortyEightAT_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortyEightAT_431 : Nat.Prime 431 := by norm_num
private theorem prime_fortyEightAT_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyEightAT_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortyEightAT_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortyEightAT_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortyEightAT_467 : Nat.Prime 467 := by norm_num
private theorem prime_fortyEightAT_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortyEightAT_487 : Nat.Prime 487 := by norm_num
private theorem prime_fortyEightAT_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyEightAT_503 : Nat.Prime 503 := by norm_num
private theorem prime_fortyEightAT_509 : Nat.Prime 509 := by norm_num
private theorem prime_fortyEightAT_521 : Nat.Prime 521 := by norm_num
private theorem prime_fortyEightAT_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortyEightAT_569 : Nat.Prime 569 := by norm_num
private theorem prime_fortyEightAT_587 : Nat.Prime 587 := by norm_num
private theorem prime_fortyEightAT_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyEightAT_607 : Nat.Prime 607 := by norm_num
private theorem prime_fortyEightAT_613 : Nat.Prime 613 := by norm_num
private theorem prime_fortyEightAT_643 : Nat.Prime 643 := by norm_num
private theorem prime_fortyEightAT_647 : Nat.Prime 647 := by norm_num
private theorem prime_fortyEightAT_653 : Nat.Prime 653 := by norm_num
private theorem prime_fortyEightAT_683 : Nat.Prime 683 := by norm_num
private theorem prime_fortyEightAT_691 : Nat.Prime 691 := by norm_num
private theorem prime_fortyEightAT_739 : Nat.Prime 739 := by norm_num
private theorem prime_fortyEightAT_757 : Nat.Prime 757 := by norm_num
private theorem prime_fortyEightAT_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyEightAT_773 : Nat.Prime 773 := by norm_num
private theorem prime_fortyEightAT_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyEightAT_821 : Nat.Prime 821 := by norm_num
private theorem prime_fortyEightAT_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortyEightAT_839 : Nat.Prime 839 := by norm_num
private theorem prime_fortyEightAT_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortyEightAT_877 : Nat.Prime 877 := by norm_num
private theorem prime_fortyEightAT_881 : Nat.Prime 881 := by norm_num
private theorem prime_fortyEightAT_907 : Nat.Prime 907 := by norm_num
private theorem prime_fortyEightAT_937 : Nat.Prime 937 := by norm_num
private theorem prime_fortyEightAT_967 : Nat.Prime 967 := by norm_num
private theorem prime_fortyEightAT_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortyEightAT_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fortyEightAT_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fortyEightAT_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortyEightAT_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fortyEightAT_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fortyEightAT_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_fortyEightAT_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_fortyEightAT_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyEightAT_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fortyEightAT_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyEightAT_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_fortyEightAT_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_fortyEightAT_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_fortyEightAT_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_fortyEightAT_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fortyEightAT_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fortyEightAT_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_fortyEightAT_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_fortyEightAT_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fortyEightAT_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_fortyEightAT_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fortyEightAT_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_fortyEightAT_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fortyEightAT_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_fortyEightAT_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fortyEightAT_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fortyEightAT_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_fortyEightAT_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_fortyEightAT_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_fortyEightAT_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_fortyEightAT_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_fortyEightAT_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_fortyEightAT_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyEightAT_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_fortyEightAT_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fortyEightAT_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_fortyEightAT_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_fortyEightAT_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fortyEightAT_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_fortyEightAT_3119 : Nat.Prime 3119 := by norm_num
private theorem prime_fortyEightAT_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_fortyEightAT_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_fortyEightAT_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_fortyEightAT_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_fortyEightAT_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_fortyEightAT_3931 : Nat.Prime 3931 := by norm_num
private theorem prime_fortyEightAT_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_fortyEightAT_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_fortyEightAT_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_fortyEightAT_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_fortyEightAT_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_fortyEightAT_4643 : Nat.Prime 4643 := by norm_num
private theorem prime_fortyEightAT_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_fortyEightAT_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_fortyEightAT_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_fortyEightAT_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_fortyEightAT_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyEightAT_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_fortyEightAT_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_fortyEightAT_5333 : Nat.Prime 5333 := by norm_num
private theorem prime_fortyEightAT_5413 : Nat.Prime 5413 := by norm_num
private theorem prime_fortyEightAT_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_fortyEightAT_5669 : Nat.Prime 5669 := by norm_num
private theorem prime_fortyEightAT_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_fortyEightAT_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_fortyEightAT_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_fortyEightAT_6317 : Nat.Prime 6317 := by norm_num
private theorem prime_fortyEightAT_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fortyEightAT_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_fortyEightAT_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyEightAT_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_fortyEightAT_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_fortyEightAT_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_fortyEightAT_7703 : Nat.Prime 7703 := by norm_num
private theorem prime_fortyEightAT_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_fortyEightAT_8209 : Nat.Prime 8209 := by norm_num
private theorem prime_fortyEightAT_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fortyEightAT_8317 : Nat.Prime 8317 := by norm_num
private theorem prime_fortyEightAT_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_fortyEightAT_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fortyEightAT_8527 : Nat.Prime 8527 := by norm_num
private theorem prime_fortyEightAT_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fortyEightAT_8747 : Nat.Prime 8747 := by norm_num
private theorem prime_fortyEightAT_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_fortyEightAT_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_fortyEightAT_9067 : Nat.Prime 9067 := by norm_num
private theorem prime_fortyEightAT_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_fortyEightAT_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_fortyEightAT_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_fortyEightAT_11447 : Nat.Prime 11447 := by norm_num
private theorem prime_fortyEightAT_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_fortyEightAT_11867 : Nat.Prime 11867 := by norm_num
private theorem prime_fortyEightAT_12323 : Nat.Prime 12323 := by norm_num
private theorem prime_fortyEightAT_12379 : Nat.Prime 12379 := by norm_num
private theorem prime_fortyEightAT_13093 : Nat.Prime 13093 := by norm_num
private theorem prime_fortyEightAT_13121 : Nat.Prime 13121 := by norm_num
private theorem prime_fortyEightAT_13309 : Nat.Prime 13309 := by norm_num
private theorem prime_fortyEightAT_13679 : Nat.Prime 13679 := by norm_num
private theorem prime_fortyEightAT_13693 : Nat.Prime 13693 := by norm_num
private theorem prime_fortyEightAT_13799 : Nat.Prime 13799 := by norm_num
private theorem prime_fortyEightAT_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_fortyEightAT_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_fortyEightAT_14489 : Nat.Prime 14489 := by norm_num
private theorem prime_fortyEightAT_14653 : Nat.Prime 14653 := by norm_num
private theorem prime_fortyEightAT_14771 : Nat.Prime 14771 := by norm_num
private theorem prime_fortyEightAT_15131 : Nat.Prime 15131 := by norm_num
private theorem prime_fortyEightAT_15137 : Nat.Prime 15137 := by norm_num
private theorem prime_fortyEightAT_15287 : Nat.Prime 15287 := by norm_num
private theorem prime_fortyEightAT_15797 : Nat.Prime 15797 := by norm_num
private theorem prime_fortyEightAT_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_fortyEightAT_17539 : Nat.Prime 17539 := by norm_num
private theorem prime_fortyEightAT_17573 : Nat.Prime 17573 := by norm_num
private theorem prime_fortyEightAT_17581 : Nat.Prime 17581 := by norm_num
private theorem prime_fortyEightAT_17737 : Nat.Prime 17737 := by norm_num
private theorem prime_fortyEightAT_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_fortyEightAT_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_fortyEightAT_19403 : Nat.Prime 19403 := by norm_num
private theorem prime_fortyEightAT_19997 : Nat.Prime 19997 := by norm_num
private theorem prime_fortyEightAT_20261 : Nat.Prime 20261 := by norm_num
private theorem prime_fortyEightAT_20551 : Nat.Prime 20551 := by norm_num
private theorem prime_fortyEightAT_21247 : Nat.Prime 21247 := by norm_num
private theorem prime_fortyEightAT_23627 : Nat.Prime 23627 := by norm_num
private theorem prime_fortyEightAT_24223 : Nat.Prime 24223 := by norm_num
private theorem prime_fortyEightAT_24923 : Nat.Prime 24923 := by norm_num
private theorem prime_fortyEightAT_26821 : Nat.Prime 26821 := by norm_num
private theorem prime_fortyEightAT_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_fortyEightAT_32099 : Nat.Prime 32099 := by norm_num
private theorem prime_fortyEightAT_32143 : Nat.Prime 32143 := by norm_num
private theorem prime_fortyEightAT_34301 : Nat.Prime 34301 := by norm_num
private theorem prime_fortyEightAT_34591 : Nat.Prime 34591 := by norm_num
private theorem prime_fortyEightAT_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyEightAT_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyEightAT_39373 : Nat.Prime 39373 := by norm_num
private theorem prime_fortyEightAT_39511 : Nat.Prime 39511 := by norm_num
private theorem prime_fortyEightAT_40597 : Nat.Prime 40597 := by norm_num
private theorem prime_fortyEightAT_42169 : Nat.Prime 42169 := by norm_num
private theorem prime_fortyEightAT_44351 : Nat.Prime 44351 := by norm_num
private theorem prime_fortyEightAT_51577 : Nat.Prime 51577 := by norm_num
private theorem prime_fortyEightAT_53173 : Nat.Prime 53173 := by norm_num
private theorem prime_fortyEightAT_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_fortyEightAT_55897 : Nat.Prime 55897 := by norm_num
private theorem prime_fortyEightAT_57791 : Nat.Prime 57791 := by norm_num
private theorem prime_fortyEightAT_58573 : Nat.Prime 58573 := by norm_num
private theorem prime_fortyEightAT_59513 : Nat.Prime 59513 := by norm_num
private theorem prime_fortyEightAT_59617 : Nat.Prime 59617 := by norm_num
private theorem prime_fortyEightAT_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_fortyEightAT_61627 : Nat.Prime 61627 := by norm_num
private theorem prime_fortyEightAT_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyEightAT_63793 : Nat.Prime 63793 := by norm_num
private theorem prime_fortyEightAT_64091 : Nat.Prime 64091 := by norm_num
private theorem prime_fortyEightAT_65129 : Nat.Prime 65129 := by norm_num
private theorem prime_fortyEightAT_66553 : Nat.Prime 66553 := by norm_num
private theorem prime_fortyEightAT_66569 : Nat.Prime 66569 := by norm_num
private theorem prime_fortyEightAT_68891 : Nat.Prime 68891 := by norm_num
private theorem prime_fortyEightAT_71171 : Nat.Prime 71171 := by norm_num
private theorem prime_fortyEightAT_75797 : Nat.Prime 75797 := by norm_num
private theorem prime_fortyEightAT_80191 : Nat.Prime 80191 := by norm_num
private theorem prime_fortyEightAT_80819 : Nat.Prime 80819 := by norm_num
private theorem prime_fortyEightAT_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fortyEightAT_82301 : Nat.Prime 82301 := by norm_num
private theorem prime_fortyEightAT_82763 : Nat.Prime 82763 := by norm_num
private theorem prime_fortyEightAT_83737 : Nat.Prime 83737 := by norm_num
private theorem prime_fortyEightAT_85243 : Nat.Prime 85243 := by norm_num
private theorem prime_fortyEightAT_85313 : Nat.Prime 85313 := by norm_num
private theorem prime_fortyEightAT_91757 : Nat.Prime 91757 := by norm_num
private theorem prime_fortyEightAT_91823 : Nat.Prime 91823 := by norm_num
private theorem prime_fortyEightAT_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fortyEightAT_96821 : Nat.Prime 96821 := by norm_num
private theorem prime_fortyEightAT_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_fortyEightAT_98869 : Nat.Prime 98869 := by norm_num
private theorem prime_fortyEightAT_102593 : Nat.Prime 102593 := by norm_num
private theorem prime_fortyEightAT_106363 : Nat.Prime 106363 := by norm_num
private theorem prime_fortyEightAT_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fortyEightAT_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_fortyEightAT_119737 : Nat.Prime 119737 := by norm_num
private theorem prime_fortyEightAT_121151 : Nat.Prime 121151 := by norm_num
private theorem prime_fortyEightAT_128239 : Nat.Prime 128239 := by norm_num
private theorem prime_fortyEightAT_137251 : Nat.Prime 137251 := by norm_num
private theorem prime_fortyEightAT_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_fortyEightAT_148721 : Nat.Prime 148721 := by norm_num
private theorem prime_fortyEightAT_153733 : Nat.Prime 153733 := by norm_num
private theorem prime_fortyEightAT_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fortyEightAT_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_fortyEightAT_169789 : Nat.Prime 169789 := by norm_num
private theorem prime_fortyEightAT_172093 : Nat.Prime 172093 := by norm_num
private theorem prime_fortyEightAT_174901 : Nat.Prime 174901 := by norm_num
private theorem prime_fortyEightAT_175141 : Nat.Prime 175141 := by norm_num
private theorem prime_fortyEightAT_176021 : Nat.Prime 176021 := by norm_num
private theorem prime_fortyEightAT_176303 : Nat.Prime 176303 := by norm_num
private theorem prime_fortyEightAT_180497 : Nat.Prime 180497 := by norm_num
private theorem prime_fortyEightAT_182467 : Nat.Prime 182467 := by norm_num
private theorem prime_fortyEightAT_183439 : Nat.Prime 183439 := by norm_num
private theorem prime_fortyEightAT_206813 : Nat.Prime 206813 := by norm_num
private theorem prime_fortyEightAT_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_fortyEightAT_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fortyEightAT_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fortyEightAT_222197 : Nat.Prime 222197 := by norm_num
private theorem prime_fortyEightAT_228023 : Nat.Prime 228023 := by norm_num
private theorem prime_fortyEightAT_229519 : Nat.Prime 229519 := by norm_num
private theorem prime_fortyEightAT_239963 : Nat.Prime 239963 := by norm_num
private theorem prime_fortyEightAT_243917 : Nat.Prime 243917 := by norm_num
private theorem prime_fortyEightAT_269783 : Nat.Prime 269783 := by norm_num
private theorem prime_fortyEightAT_272347 : Nat.Prime 272347 := by norm_num
private theorem prime_fortyEightAT_280097 : Nat.Prime 280097 := by norm_num
private theorem prime_fortyEightAT_315103 : Nat.Prime 315103 := by norm_num
private theorem prime_fortyEightAT_319489 : Nat.Prime 319489 := by norm_num
private theorem prime_fortyEightAT_338753 : Nat.Prime 338753 := by norm_num
private theorem prime_fortyEightAT_372377 : Nat.Prime 372377 := by norm_num
private theorem prime_fortyEightAT_381761 : Nat.Prime 381761 := by norm_num
private theorem prime_fortyEightAT_382709 : Nat.Prime 382709 := by norm_num
private theorem prime_fortyEightAT_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_fortyEightAT_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_fortyEightAT_402137 : Nat.Prime 402137 := by norm_num
private theorem prime_fortyEightAT_473021 : Nat.Prime 473021 := by norm_num
private theorem prime_fortyEightAT_527381 : Nat.Prime 527381 := by norm_num
private theorem prime_fortyEightAT_576617 : Nat.Prime 576617 := by norm_num
private theorem prime_fortyEightAT_595201 : Nat.Prime 595201 := by norm_num
private theorem prime_fortyEightAT_637519 : Nat.Prime 637519 := by norm_num
private theorem prime_fortyEightAT_653273 : Nat.Prime 653273 := by norm_num
private theorem prime_fortyEightAT_661009 : Nat.Prime 661009 := by norm_num
private theorem prime_fortyEightAT_670673 : Nat.Prime 670673 := by norm_num
private theorem prime_fortyEightAT_674701 : Nat.Prime 674701 := by norm_num
private theorem prime_fortyEightAT_742681 : Nat.Prime 742681 := by norm_num
private theorem prime_fortyEightAT_813613 : Nat.Prime 813613 := by norm_num
private theorem prime_fortyEightAT_862819 : Nat.Prime 862819 := by norm_num
private theorem prime_fortyEightAT_897907 : Nat.Prime 897907 := by norm_num
private theorem prime_fortyEightAT_965551 : Nat.Prime 965551 := by norm_num
private theorem prime_fortyEightAT_992263 : Nat.Prime 992263 := by norm_num
private theorem prime_fortyEightAT_1036459 : Nat.Prime 1036459 := by norm_num
private theorem prime_fortyEightAT_1071979 : Nat.Prime 1071979 := by norm_num
private theorem prime_fortyEightAT_1125193 : Nat.Prime 1125193 := by norm_num
private theorem prime_fortyEightAT_1127537 : Nat.Prime 1127537 := by norm_num
private theorem prime_fortyEightAT_1228273 : Nat.Prime 1228273 := by norm_num
private theorem prime_fortyEightAT_1257209 : Nat.Prime 1257209 := by norm_num
private theorem prime_fortyEightAT_1265779 : Nat.Prime 1265779 := by norm_num
private theorem prime_fortyEightAT_1333261 : Nat.Prime 1333261 := by norm_num
private theorem prime_fortyEightAT_1427389 : Nat.Prime 1427389 := by norm_num
private theorem prime_fortyEightAT_1458229 : Nat.Prime 1458229 := by norm_num
private theorem prime_fortyEightAT_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fortyEightAT_1752871 : Nat.Prime 1752871 := by norm_num
private theorem prime_fortyEightAT_1805911 : Nat.Prime 1805911 := by norm_num
private theorem prime_fortyEightAT_1856137 : Nat.Prime 1856137 := by norm_num
private theorem prime_fortyEightAT_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_fortyEightAT_1934663 : Nat.Prime 1934663 := by norm_num
private theorem prime_fortyEightAT_1965553 : Nat.Prime 1965553 := by norm_num
private theorem prime_fortyEightAT_1976731 : Nat.Prime 1976731 := by norm_num
private theorem prime_fortyEightAT_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fortyEightAT_2112239 : Nat.Prime 2112239 := by norm_num
private theorem prime_fortyEightAT_2183231 : Nat.Prime 2183231 := by norm_num
private theorem prime_fortyEightAT_2270447 : Nat.Prime 2270447 := by norm_num
private theorem prime_fortyEightAT_2379253 : Nat.Prime 2379253 := by norm_num
private theorem prime_fortyEightAT_2422033 : Nat.Prime 2422033 := by norm_num
private theorem prime_fortyEightAT_2516201 : Nat.Prime 2516201 := by norm_num
private theorem prime_fortyEightAT_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fortyEightAT_2751247 : Nat.Prime 2751247 := by norm_num
private theorem prime_fortyEightAT_2847931 : Nat.Prime 2847931 := by norm_num
private theorem prime_fortyEightAT_3427799 : Nat.Prime 3427799 := by norm_num
private theorem prime_fortyEightAT_3542327 : Nat.Prime 3542327 := by norm_num
private theorem prime_fortyEightAT_3743237 : Nat.Prime 3743237 := by norm_num
private theorem prime_fortyEightAT_3972037 : Nat.Prime 3972037 := by norm_num
private theorem prime_fortyEightAT_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_fortyEightAT_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_fortyEightAT_4203707 : Nat.Prime 4203707 := by norm_num
private theorem prime_fortyEightAT_4315799 : Nat.Prime 4315799 := by norm_num
private theorem prime_fortyEightAT_4613533 : Nat.Prime 4613533 := by norm_num
private theorem prime_fortyEightAT_4787273 : Nat.Prime 4787273 := by norm_num
private theorem prime_fortyEightAT_4791049 : Nat.Prime 4791049 := by norm_num
private theorem prime_fortyEightAT_4924417 : Nat.Prime 4924417 := by norm_num
private theorem prime_fortyEightAT_5400053 : Nat.Prime 5400053 := by norm_num
private theorem prime_fortyEightAT_5809847 : Nat.Prime 5809847 := by norm_num
private theorem prime_fortyEightAT_5841559 : Nat.Prime 5841559 := by norm_num
private theorem prime_fortyEightAT_6305347 : Nat.Prime 6305347 := by norm_num
private theorem prime_fortyEightAT_6415831 : Nat.Prime 6415831 := by norm_num
private theorem prime_fortyEightAT_6850243 : Nat.Prime 6850243 := by norm_num
private theorem prime_fortyEightAT_6895393 : Nat.Prime 6895393 := by norm_num
private theorem prime_fortyEightAT_7041049 : Nat.Prime 7041049 := by norm_num
private theorem prime_fortyEightAT_7145597 : Nat.Prime 7145597 := by norm_num
private theorem prime_fortyEightAT_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyEightAT_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_fortyEightAT_7281277 : Nat.Prime 7281277 := by norm_num
private theorem prime_fortyEightAT_7704943 : Nat.Prime 7704943 := by norm_num
private theorem prime_fortyEightAT_8265919 : Nat.Prime 8265919 := by norm_num
private theorem prime_fortyEightAT_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fortyEightAT_8526929 : Nat.Prime 8526929 := by norm_num
private theorem prime_fortyEightAT_8596663 : Nat.Prime 8596663 := by norm_num
private theorem prime_fortyEightAT_9124861 : Nat.Prime 9124861 := by norm_num
private theorem prime_fortyEightAT_9574219 : Nat.Prime 9574219 := by norm_num
private theorem prime_fortyEightAT_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fortyEightAT_11782181 : Nat.Prime 11782181 := by norm_num
private theorem prime_fortyEightAT_12444181 : Nat.Prime 12444181 := by norm_num
private theorem prime_fortyEightAT_13992131 : Nat.Prime 13992131 := by norm_num
private theorem prime_fortyEightAT_14467279 : Nat.Prime 14467279 := by norm_num
private theorem prime_fortyEightAT_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fortyEightAT_16205789 : Nat.Prime 16205789 := by norm_num
private theorem prime_fortyEightAT_16230371 : Nat.Prime 16230371 := by norm_num
private theorem prime_fortyEightAT_16480507 : Nat.Prime 16480507 := by norm_num
private theorem prime_fortyEightAT_17272207 : Nat.Prime 17272207 := by norm_num
private theorem prime_fortyEightAT_17478479 : Nat.Prime 17478479 := by norm_num
private theorem prime_fortyEightAT_18373307 : Nat.Prime 18373307 := by norm_num
private theorem prime_fortyEightAT_18480383 : Nat.Prime 18480383 := by norm_num
private theorem prime_fortyEightAT_20538307 : Nat.Prime 20538307 := by norm_num
private theorem prime_fortyEightAT_21706837 : Nat.Prime 21706837 := by norm_num
private theorem prime_fortyEightAT_23137643 : Nat.Prime 23137643 := by norm_num
private theorem prime_fortyEightAT_23255671 : Nat.Prime 23255671 := by norm_num
private theorem prime_fortyEightAT_24581699 : Nat.Prime 24581699 := by norm_num
private theorem prime_fortyEightAT_25331881 : Nat.Prime 25331881 := by norm_num
private theorem prime_fortyEightAT_25817069 : Nat.Prime 25817069 := by norm_num
private theorem prime_fortyEightAT_27902741 : Nat.Prime 27902741 := by norm_num

private theorem prime_fortyEightAT_39926713 : Nat.Prime 39926713 := by
  apply lucas_primality 39926713 (11 : ZMod 39926713)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 39926713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39926713) ^ 19963356 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 13308904 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 5703816 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 1735944 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 3864 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_40902889 : Nat.Prime 40902889 := by
  apply lucas_primality 40902889 (7 : ZMod 40902889)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (31, 1), (4229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (31, 1), (4229, 1)] : List FactorBlock).map factorBlockValue).prod) = 40902889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_4229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 40902889) ^ 20451444 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 40902889) ^ 13634296 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 40902889) ^ 3146376 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 40902889) ^ 1319448 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 40902889) ^ 9672 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_41136839 : Nat.Prime 41136839 := by
  apply lucas_primality 41136839 (7 : ZMod 41136839)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) = 41136839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_71171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 41136839) ^ 20568419 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 2419814 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 578 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_42001217 : Nat.Prime 42001217 := by
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42001217) ^ 21000608 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 1135168 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 2368 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_42690547 : Nat.Prime 42690547 := by
  apply lucas_primality 42690547 (3 : ZMod 42690547)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (73, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (73, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 42690547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_73
      · exact prime_fortyEightAT_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42690547) ^ 21345273 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42690547) ^ 14230182 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42690547) ^ 805482 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42690547) ^ 584802 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 42690547) ^ 69642 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_43687663 : Nat.Prime 43687663 := by
  apply lucas_primality 43687663 (3 : ZMod 43687663)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) = 43687663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7281277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43687663) ^ 21843831 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 14562554 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 6 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_45381451 : Nat.Prime 45381451 := by
  apply lucas_primality 45381451 (10 : ZMod 45381451)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (97, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (97, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod) = 45381451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_97
      · exact prime_fortyEightAT_3119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 45381451) ^ 22690725 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 45381451) ^ 15127150 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 45381451) ^ 9076290 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 45381451) ^ 467850 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 45381451) ^ 14550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_47910491 : Nat.Prime 47910491 := by
  apply lucas_primality 47910491 (2 : ZMod 47910491)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4791049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4791049, 1)] : List FactorBlock).map factorBlockValue).prod) = 47910491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_4791049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47910491) ^ 23955245 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 47910491) ^ 9582098 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 47910491) ^ 10 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_51634139 : Nat.Prime 51634139 := by
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51634139) ^ 25817069 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 51634139) ^ 2 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_57122173 : Nat.Prime 57122173 := by
  apply lucas_primality 57122173 (5 : ZMod 57122173)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (176303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (176303, 1)] : List FactorBlock).map factorBlockValue).prod) = 57122173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_176303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 57122173) ^ 28561086 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 57122173) ^ 19040724 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 57122173) ^ 324 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_66828803 : Nat.Prime 66828803 := by
  apply lucas_primality 66828803 (2 : ZMod 66828803)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod) = 66828803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_1965553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66828803) ^ 33414401 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 3931106 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 34 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_69088829 : Nat.Prime 69088829 := by
  apply lucas_primality 69088829 (2 : ZMod 69088829)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17272207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17272207, 1)] : List FactorBlock).map factorBlockValue).prod) = 69088829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17272207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 69088829) ^ 34544414 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 69088829) ^ 4 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_70150373 : Nat.Prime 70150373 := by
  apply lucas_primality 70150373 (2 : ZMod 70150373)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 70150373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_73
      · exact prime_fortyEightAT_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70150373) ^ 35075186 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1895956 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1631404 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 960964 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 464572 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_1901
      · exact prime_fortyEightAT_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_73588961 : Nat.Prime 73588961 := by
  apply lucas_primality 73588961 (3 : ZMod 73588961)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (23, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (23, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) = 73588961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_19997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73588961) ^ 36794480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 73588961) ^ 14717792 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 73588961) ^ 3199520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 73588961) ^ 3680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_73816529 : Nat.Prime 73816529 := by
  apply lucas_primality 73816529 (3 : ZMod 73816529)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod) = 73816529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_4613533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73816529) ^ 36908264 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 73816529) ^ 16 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_100284931 : Nat.Prime 100284931 := by
  apply lucas_primality 100284931 (2 : ZMod 100284931)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (67, 1), (16631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (67, 1), (16631, 1)] : List FactorBlock).map factorBlockValue).prod) = 100284931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_16631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100284931) ^ 50142465 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 100284931) ^ 33428310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 100284931) ^ 20056986 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 100284931) ^ 1496790 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 100284931) ^ 6030 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_100888969 : Nat.Prime 100888969 := by
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100888969) ^ 50444484 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 33629656 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 24 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_115484959 : Nat.Prime 115484959 := by
  apply lucas_primality 115484959 (6 : ZMod 115484959)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6415831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6415831, 1)] : List FactorBlock).map factorBlockValue).prod) = 115484959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_6415831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 115484959) ^ 57742479 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 115484959) ^ 38494986 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 115484959) ^ 18 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_115620599 : Nat.Prime 115620599 := by
  apply lucas_primality 115620599 (17 : ZMod 115620599)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1801, 1), (32099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1801, 1), (32099, 1)] : List FactorBlock).map factorBlockValue).prod) = 115620599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_1801
      · exact prime_fortyEightAT_32099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 115620599) ^ 57810299 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 115620599) ^ 64198 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 115620599) ^ 3602 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_129716129 : Nat.Prime 129716129 := by
  apply lucas_primality 129716129 (3 : ZMod 129716129)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (98869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (98869, 1)] : List FactorBlock).map factorBlockValue).prod) = 129716129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_98869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129716129) ^ 64858064 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 129716129) ^ 3163808 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 129716129) ^ 1312 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_131367307 : Nat.Prime 131367307 := by
  apply lucas_primality 131367307 (3 : ZMod 131367307)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (239, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (239, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 131367307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_239
      · exact prime_fortyEightAT_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131367307) ^ 65683653 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 43789102 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 18766758 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 5711622 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 549654 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 230874 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_153026249 : Nat.Prime 153026249 := by
  apply lucas_primality 153026249 (3 : ZMod 153026249)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1125193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1125193, 1)] : List FactorBlock).map factorBlockValue).prod) = 153026249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_1125193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 153026249) ^ 76513124 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 153026249) ^ 9001544 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 153026249) ^ 136 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_131
      · exact prime_fortyEightAT_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_219857951 : Nat.Prime 219857951 := by
  apply lucas_primality 219857951 (17 : ZMod 219857951)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) = 219857951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_409
      · exact prime_fortyEightAT_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 219857951) ^ 109928975 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 43971590 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 16912150 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 537550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 265850 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_219959393 : Nat.Prime 219959393 := by
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219959393) ^ 109979696 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 3282976 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 2144 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_191
      · exact prime_fortyEightAT_383
      · exact prime_fortyEightAT_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_259432259 : Nat.Prime 259432259 := by
  apply lucas_primality 259432259 (2 : ZMod 259432259)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (129716129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (129716129, 1)] : List FactorBlock).map factorBlockValue).prod) = 259432259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_129716129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 259432259) ^ 129716129 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 259432259) ^ 2 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_260551547 : Nat.Prime 260551547 := by
  apply lucas_primality 260551547 (2 : ZMod 260551547)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod) = 260551547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3209
      · exact prime_fortyEightAT_40597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 260551547) ^ 130275773 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 81194 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 6418 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_266476337 : Nat.Prime 266476337 := by
  apply lucas_primality 266476337 (3 : ZMod 266476337)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) = 266476337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_2379253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266476337) ^ 133238168 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 38068048 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 112 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_276413069 : Nat.Prime 276413069 := by
  apply lucas_primality 276413069 (2 : ZMod 276413069)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (311, 1), (222197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (311, 1), (222197, 1)] : List FactorBlock).map factorBlockValue).prod) = 276413069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_311
      · exact prime_fortyEightAT_222197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276413069) ^ 138206534 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 276413069) ^ 888788 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 276413069) ^ 1244 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_289267687 : Nat.Prime 289267687 := by
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 289267687) ^ 144633843 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 96422562 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 486 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_324023303 : Nat.Prime 324023303 := by
  apply lucas_primality 324023303 (5 : ZMod 324023303)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod) = 324023303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_8526929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 324023303) ^ 162011651 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 17053858 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 38 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_362808133 : Nat.Prime 362808133 := by
  apply lucas_primality 362808133 (5 : ZMod 362808133)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) = 362808133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_79
      · exact prime_fortyEightAT_382709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 362808133) ^ 181404066 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 120936044 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 4592508 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 948 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_441374291 : Nat.Prime 441374291 := by
  apply lucas_primality 441374291 (6 : ZMod 441374291)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod) = 441374291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_6305347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 441374291) ^ 220687145 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 88274858 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 63053470 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 70 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_475609213 : Nat.Prime 475609213 := by
  apply lucas_primality 475609213 (2 : ZMod 475609213)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (338753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (338753, 1)] : List FactorBlock).map factorBlockValue).prod) = 475609213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_338753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 475609213) ^ 237804606 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 475609213) ^ 158536404 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 475609213) ^ 36585324 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 475609213) ^ 1404 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_539315099 : Nat.Prime 539315099 := by
  apply lucas_primality 539315099 (2 : ZMod 539315099)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) = 539315099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_4603
      · exact prime_fortyEightAT_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 539315099) ^ 269657549 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 77045014 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 117166 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 64442 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_642191821 : Nat.Prime 642191821 := by
  apply lucas_primality 642191821 (2 : ZMod 642191821)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) = 642191821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_167
      · exact prime_fortyEightAT_64091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642191821) ^ 321095910 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 214063940 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 128438364 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 3845460 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 10020 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_679963111 : Nat.Prime 679963111 := by
  apply lucas_primality 679963111 (3 : ZMod 679963111)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (1333261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (1333261, 1)] : List FactorBlock).map factorBlockValue).prod) = 679963111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_1333261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 679963111) ^ 339981555 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 679963111) ^ 226654370 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 679963111) ^ 135992622 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 679963111) ^ 39997830 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 679963111) ^ 510 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_685466077 : Nat.Prime 685466077 := by
  apply lucas_primality 685466077 (6 : ZMod 685466077)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (57122173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (57122173, 1)] : List FactorBlock).map factorBlockValue).prod) = 685466077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_57122173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 685466077) ^ 342733038 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 685466077) ^ 228488692 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 685466077) ^ 12 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_687793297 : Nat.Prime 687793297 := by
  apply lucas_primality 687793297 (5 : ZMod 687793297)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (53, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (53, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) = 687793297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 687793297) ^ 343896648 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 687793297) ^ 229264432 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 687793297) ^ 18589008 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 687793297) ^ 12977232 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 687793297) ^ 94128 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_710369951 : Nat.Prime 710369951 := by
  apply lucas_primality 710369951 (7 : ZMod 710369951)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 710369951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_557
      · exact prime_fortyEightAT_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 710369951) ^ 355184975 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 142073990 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 30885650 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 1275350 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 640550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_752298509 : Nat.Prime 752298509 := by
  apply lucas_primality 752298509 (2 : ZMod 752298509)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod) = 752298509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_14467279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 752298509) ^ 376149254 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 57869116 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 52 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_922507631 : Nat.Prime 922507631 := by
  apply lucas_primality 922507631 (11 : ZMod 922507631)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (443, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (443, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) = 922507631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_443
      · exact prime_fortyEightAT_1721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 922507631) ^ 461253815 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 184501526 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 83864330 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 2082410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 536030 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_930659839 : Nat.Prime 930659839 := by
  apply lucas_primality 930659839 (3 : ZMod 930659839)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) = 930659839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_269
      · exact prime_fortyEightAT_576617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 930659839) ^ 465329919 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 310219946 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 3459702 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 1614 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_960259579 : Nat.Prime 960259579 := by
  apply lucas_primality 960259579 (2 : ZMod 960259579)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 2), (8527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 2), (8527, 1)] : List FactorBlock).map factorBlockValue).prod) = 960259579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_137
      · exact prime_fortyEightAT_8527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 960259579) ^ 480129789 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 960259579) ^ 320086526 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 960259579) ^ 7009194 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 960259579) ^ 112614 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_971781007 : Nat.Prime 971781007 := by
  apply lucas_primality 971781007 (3 : ZMod 971781007)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23137643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23137643, 1)] : List FactorBlock).map factorBlockValue).prod) = 971781007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_23137643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 971781007) ^ 485890503 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 323927002 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 138825858 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 42 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_985098929 : Nat.Prime 985098929 := by
  apply lucas_primality 985098929 (3 : ZMod 985098929)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (59, 1), (4993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (59, 1), (4993, 1)] : List FactorBlock).map factorBlockValue).prod) = 985098929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_4993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 985098929) ^ 492549464 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 985098929) ^ 89554448 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 985098929) ^ 51847312 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 985098929) ^ 16696592 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 985098929) ^ 197296 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1113884029 : Nat.Prime 1113884029 := by
  apply lucas_primality 1113884029 (2 : ZMod 1113884029)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (173, 1), (59617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (173, 1), (59617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113884029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_173
      · exact prime_fortyEightAT_59617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1113884029) ^ 556942014 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113884029) ^ 371294676 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113884029) ^ 6438636 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113884029) ^ 18684 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1131173671 : Nat.Prime 1131173671 := by
  apply lucas_primality 1131173671 (3 : ZMod 1131173671)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (3427799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (3427799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1131173671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_3427799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1131173671) ^ 565586835 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 377057890 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 226234734 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 102833970 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 330 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1137886639 : Nat.Prime 1137886639 := by
  apply lucas_primality 1137886639 (3 : ZMod 1137886639)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (277, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (277, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137886639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_277
      · exact prime_fortyEightAT_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1137886639) ^ 568943319 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 379295546 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 162555234 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 24210354 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 4107894 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 546798 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1206886753 : Nat.Prime 1206886753 := by
  apply lucas_primality 1206886753 (5 : ZMod 1206886753)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (173, 1), (24223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (173, 1), (24223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1206886753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_173
      · exact prime_fortyEightAT_24223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1206886753) ^ 603443376 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1206886753) ^ 402295584 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1206886753) ^ 6976224 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1206886753) ^ 49824 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_113
      · exact prime_fortyEightAT_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1238163221 : Nat.Prime 1238163221 := by
  apply lucas_primality 1238163221 (3 : ZMod 1238163221)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (73, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (73, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238163221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_73
      · exact prime_fortyEightAT_121151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1238163221) ^ 619081610 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 247632644 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 176880460 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 16961140 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 10220 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1244387117 : Nat.Prime 1244387117 := by
  apply lucas_primality 1244387117 (2 : ZMod 1244387117)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1657, 1), (26821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1657, 1), (26821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244387117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_1657
      · exact prime_fortyEightAT_26821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1244387117) ^ 622193558 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244387117) ^ 177769588 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244387117) ^ 750988 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244387117) ^ 46396 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1440916409 : Nat.Prime 1440916409 := by
  apply lucas_primality 1440916409 (3 : ZMod 1440916409)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440916409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_89
      · exact prime_fortyEightAT_34301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1440916409) ^ 720458204 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 24422312 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 16190072 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 42008 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1596046247 : Nat.Prime 1596046247 := by
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1596046247) ^ 798023123 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 84002434 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 38 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1656564227 : Nat.Prime 1656564227 := by
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_101
      · exact prime_fortyEightAT_2521
      · exact prime_fortyEightAT_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1656564227) ^ 828282113 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 16401626 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 657106 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 509242 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1658131897 : Nat.Prime 1658131897 := by
  apply lucas_primality 1658131897 (10 : ZMod 1658131897)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (69088829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (69088829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1658131897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_69088829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1658131897) ^ 829065948 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 1658131897) ^ 552710632 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 1658131897) ^ 24 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1705633957 : Nat.Prime 1705633957 := by
  apply lucas_primality 1705633957 (5 : ZMod 1705633957)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (29, 1), (163, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (29, 1), (163, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1705633957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_163
      · exact prime_fortyEightAT_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1705633957) ^ 852816978 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 568544652 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 131202612 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 58814964 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 10464012 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 6636708 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1836314989 : Nat.Prime 1836314989 := by
  apply lucas_primality 1836314989 (2 : ZMod 1836314989)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (153026249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (153026249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1836314989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_153026249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1836314989) ^ 918157494 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1836314989) ^ 612104996 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1836314989) ^ 12 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1917074879 : Nat.Prime 1917074879 := by
  apply lucas_primality 1917074879 (11 : ZMod 1917074879)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11447, 1), (83737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11447, 1), (83737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1917074879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11447
      · exact prime_fortyEightAT_83737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1917074879) ^ 958537439 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 1917074879) ^ 167474 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 1917074879) ^ 22894 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2770559041 : Nat.Prime 2770559041 := by
  apply lucas_primality 2770559041 (22 : ZMod 2770559041)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (347, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (347, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) = 2770559041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_347
      · exact prime_fortyEightAT_8317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2770559041) ^ 1385279520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (22 : ZMod 2770559041) ^ 923519680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (22 : ZMod 2770559041) ^ 554111808 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (22 : ZMod 2770559041) ^ 7984320 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (22 : ZMod 2770559041) ^ 333120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3141170261 : Nat.Prime 3141170261 := by
  apply lucas_primality 3141170261 (3 : ZMod 3141170261)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 2), (337, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 2), (337, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3141170261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_337
      · exact prime_fortyEightAT_881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3141170261) ^ 1570585130 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 3141170261) ^ 628234052 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 3141170261) ^ 136572620 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 3141170261) ^ 9320980 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 3141170261) ^ 3565460 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_4126759783 : Nat.Prime 4126759783 := by
  apply lucas_primality 4126759783 (3 : ZMod 4126759783)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (687793297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (687793297, 1)] : List FactorBlock).map factorBlockValue).prod) = 4126759783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_687793297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4126759783) ^ 2063379891 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4126759783) ^ 1375586594 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4126759783) ^ 6 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_5411288681 : Nat.Prime 5411288681 := by
  apply lucas_primality 5411288681 (3 : ZMod 5411288681)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) = 5411288681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_241
      · exact prime_fortyEightAT_80191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5411288681) ^ 2705644340 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 1082257736 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 773041240 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 22453480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 67480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_89
      · exact prime_fortyEightAT_223
      · exact prime_fortyEightAT_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6733751111 : Nat.Prime 6733751111 := by
  apply lucas_primality 6733751111 (19 : ZMod 6733751111)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2137, 1), (315103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2137, 1), (315103, 1)] : List FactorBlock).map factorBlockValue).prod) = 6733751111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_2137
      · exact prime_fortyEightAT_315103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 6733751111) ^ 3366875555 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 1346750222 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 3151030 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 21370 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6900728287 : Nat.Prime 6900728287 := by
  apply lucas_primality 6900728287 (3 : ZMod 6900728287)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (103, 1), (272347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (103, 1), (272347, 1)] : List FactorBlock).map factorBlockValue).prod) = 6900728287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_103
      · exact prime_fortyEightAT_272347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6900728287) ^ 3450364143 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 6900728287) ^ 2300242762 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 6900728287) ^ 168310446 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 6900728287) ^ 66997362 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 6900728287) ^ 25338 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_7467275083 : Nat.Prime 7467275083 := by
  apply lucas_primality 7467275083 (3 : ZMod 7467275083)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (2847931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (2847931, 1)] : List FactorBlock).map factorBlockValue).prod) = 7467275083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_2847931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7467275083) ^ 3733637541 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7467275083) ^ 2489091694 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7467275083) ^ 393014478 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7467275083) ^ 324664134 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7467275083) ^ 2622 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_7647016217 : Nat.Prime 7647016217 := by
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_7549
      · exact prime_fortyEightAT_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7647016217) ^ 3823508108 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1092430888 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1012984 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 422744 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_1997
      · exact prime_fortyEightAT_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_7742102567 : Nat.Prime 7742102567 := by
  apply lucas_primality 7742102567 (5 : ZMod 7742102567)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (29, 1), (113, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (29, 1), (113, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 7742102567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_113
      · exact prime_fortyEightAT_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7742102567) ^ 3871051283 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7742102567) ^ 703827506 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7742102567) ^ 455417798 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7742102567) ^ 266969054 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7742102567) ^ 68514182 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 7742102567) ^ 1225598 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8784511289 : Nat.Prime 8784511289 := by
  apply lucas_primality 8784511289 (3 : ZMod 8784511289)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8784511289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_167
      · exact prime_fortyEightAT_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8784511289) ^ 4392255644 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 1254930184 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 237419224 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 165745496 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 52601864 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 18339272 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9428965463 : Nat.Prime 9428965463 := by
  apply lucas_primality 9428965463 (5 : ZMod 9428965463)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103, 1), (337, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103, 1), (337, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod) = 9428965463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_103
      · exact prime_fortyEightAT_337
      · exact prime_fortyEightAT_19403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9428965463) ^ 4714482731 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 1346995066 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 91543354 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 27979126 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 485954 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9702444491 : Nat.Prime 9702444491 := by
  apply lucas_primality 9702444491 (2 : ZMod 9702444491)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (167, 1), (5809847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (167, 1), (5809847, 1)] : List FactorBlock).map factorBlockValue).prod) = 9702444491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_167
      · exact prime_fortyEightAT_5809847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9702444491) ^ 4851222245 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9702444491) ^ 1940488898 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9702444491) ^ 58098470 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9702444491) ^ 1670 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9939346271 : Nat.Prime 9939346271 := by
  apply lucas_primality 9939346271 (14 : ZMod 9939346271)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (2131, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (2131, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) = 9939346271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_2131
      · exact prime_fortyEightAT_2897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 9939346271) ^ 4969673135 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 1987869254 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 1419906610 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 432145490 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 4664170 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 3430910 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_10800222241 : Nat.Prime 10800222241 := by
  apply lucas_primality 10800222241 (11 : ZMod 10800222241)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23, 1), (127, 1), (7703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23, 1), (127, 1), (7703, 1)] : List FactorBlock).map factorBlockValue).prod) = 10800222241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_127
      · exact prime_fortyEightAT_7703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10800222241) ^ 5400111120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 3600074080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 2160044448 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 469574880 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 85041120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 1402080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_10892708831 : Nat.Prime 10892708831 := by
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10892708831) ^ 5446354415 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 2178541766 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 253318810 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 430 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_11527331273 : Nat.Prime 11527331273 := by
  apply lucas_primality 11527331273 (3 : ZMod 11527331273)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) = 11527331273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_1440916409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11527331273) ^ 5763665636 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 11527331273) ^ 8 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_13053027349 : Nat.Prime 13053027349 := by
  apply lucas_primality 13053027349 (2 : ZMod 13053027349)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) = 13053027349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_1511
      · exact prime_fortyEightAT_239963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13053027349) ^ 6526513674 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 4351009116 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 8638668 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 54396 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_14737656217 : Nat.Prime 14737656217 := by
  apply lucas_primality 14737656217 (10 : ZMod 14737656217)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) = 14737656217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_4129
      · exact prime_fortyEightAT_148721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 14737656217) ^ 7368828108 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 4912552072 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 3569304 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 99096 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_15040590709 : Nat.Prime 15040590709 := by
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_311
      · exact prime_fortyEightAT_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15040590709) ^ 7520295354 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 5013530236 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1367326428 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1156968516 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 48362028 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 533676 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_16089506899 : Nat.Prime 16089506899 := by
  apply lucas_primality 16089506899 (7 : ZMod 16089506899)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (67, 1), (877, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (67, 1), (877, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 16089506899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_877
      · exact prime_fortyEightAT_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16089506899) ^ 8044753449 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 5363168966 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 342329934 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 240141894 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 18346074 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 16570038 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_16713652379 : Nat.Prime 16713652379 := by
  apply lucas_primality 16713652379 (2 : ZMod 16713652379)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (13799, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (13799, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod) = 16713652379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_13799
      · exact prime_fortyEightAT_14771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16713652379) ^ 8356826189 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 407650058 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 1211222 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 1131518 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_18925287739 : Nat.Prime 18925287739 := by
  apply lucas_primality 18925287739 (2 : ZMod 18925287739)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (157, 1), (58573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (157, 1), (58573, 1)] : List FactorBlock).map factorBlockValue).prod) = 18925287739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_157
      · exact prime_fortyEightAT_58573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18925287739) ^ 9462643869 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 18925287739) ^ 6308429246 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 18925287739) ^ 2703612534 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 18925287739) ^ 120543234 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 18925287739) ^ 323106 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_19863412949 : Nat.Prime 19863412949 := by
  apply lucas_primality 19863412949 (2 : ZMod 19863412949)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (115484959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (115484959, 1)] : List FactorBlock).map factorBlockValue).prod) = 19863412949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_115484959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19863412949) ^ 9931706474 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 19863412949) ^ 461939836 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 19863412949) ^ 172 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_20785154287 : Nat.Prime 20785154287 := by
  apply lucas_primality 20785154287 (3 : ZMod 20785154287)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) = 20785154287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_266476337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20785154287) ^ 10392577143 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 6928384762 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 1598858022 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 78 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_21207925801 : Nat.Prime 21207925801 := by
  apply lucas_primality 21207925801 (14 : ZMod 21207925801)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (11782181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (11782181, 1)] : List FactorBlock).map factorBlockValue).prod) = 21207925801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11782181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 21207925801) ^ 10603962900 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 21207925801) ^ 7069308600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 21207925801) ^ 4241585160 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (14 : ZMod 21207925801) ^ 1800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_23959559521 : Nat.Prime 23959559521 := by
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_191
      · exact prime_fortyEightAT_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23959559521) ^ 11979779760 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 7986519840 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 4791911904 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 1843043040 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 125442720 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 3575520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_25194922801 : Nat.Prime 25194922801 := by
  apply lucas_primality 25194922801 (7 : ZMod 25194922801)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (277, 1), (75797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (277, 1), (75797, 1)] : List FactorBlock).map factorBlockValue).prod) = 25194922801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_277
      · exact prime_fortyEightAT_75797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 25194922801) ^ 12597461400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 25194922801) ^ 8398307600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 25194922801) ^ 5038984560 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 25194922801) ^ 90956400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 25194922801) ^ 332400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_26620044299 : Nat.Prime 26620044299 := by
  apply lucas_primality 26620044299 (2 : ZMod 26620044299)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) = 26620044299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_6850243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26620044299) ^ 13310022149 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 917932562 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 397314094 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 3886 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_71
      · exact prime_fortyEightAT_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_131
      · exact prime_fortyEightAT_149
      · exact prime_fortyEightAT_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_35115478373 : Nat.Prime 35115478373 := by
  apply lucas_primality 35115478373 (3 : ZMod 35115478373)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (13093, 1), (51577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (13093, 1), (51577, 1)] : List FactorBlock).map factorBlockValue).prod) = 35115478373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_13093
      · exact prime_fortyEightAT_51577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35115478373) ^ 17557739186 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 2701190644 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 2682004 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 680836 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_151
      · exact prime_fortyEightAT_479
      · exact prime_fortyEightAT_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_45874732741 : Nat.Prime 45874732741 := by
  apply lucas_primality 45874732741 (2 : ZMod 45874732741)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (107, 1), (7145597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (107, 1), (7145597, 1)] : List FactorBlock).map factorBlockValue).prod) = 45874732741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_107
      · exact prime_fortyEightAT_7145597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45874732741) ^ 22937366370 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 45874732741) ^ 15291577580 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 45874732741) ^ 9174946548 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 45874732741) ^ 428735820 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 45874732741) ^ 6420 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_54620595583 : Nat.Prime 54620595583 := by
  apply lucas_primality 54620595583 (3 : ZMod 54620595583)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4643, 1), (280097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4643, 1), (280097, 1)] : List FactorBlock).map factorBlockValue).prod) = 54620595583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_4643
      · exact prime_fortyEightAT_280097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54620595583) ^ 27310297791 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 54620595583) ^ 18206865194 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 54620595583) ^ 7802942226 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 54620595583) ^ 11764074 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 54620595583) ^ 195006 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_54675980063 : Nat.Prime 54675980063 := by
  apply lucas_primality 54675980063 (5 : ZMod 54675980063)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) = 54675980063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_197
      · exact prime_fortyEightAT_206813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54675980063) ^ 27337990031 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 4970543642 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 896327542 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 277543046 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 264374 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_60083373169 : Nat.Prime 60083373169 := by
  apply lucas_primality 60083373169 (11 : ZMod 60083373169)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 60083373169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_353
      · exact prime_fortyEightAT_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 60083373169) ^ 30041686584 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 20027791056 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 8583339024 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 4621797936 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 1938173328 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 170207856 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 143397072 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_61936820537 : Nat.Prime 61936820537 := by
  apply lucas_primality 61936820537 (3 : ZMod 61936820537)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7742102567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7742102567, 1)] : List FactorBlock).map factorBlockValue).prod) = 61936820537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7742102567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 61936820537) ^ 30968410268 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 61936820537) ^ 8 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_62124902789 : Nat.Prime 62124902789 := by
  apply lucas_primality 62124902789 (2 : ZMod 62124902789)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (103, 1), (937, 1), (12379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (103, 1), (937, 1), (12379, 1)] : List FactorBlock).map factorBlockValue).prod) = 62124902789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_103
      · exact prime_fortyEightAT_937
      · exact prime_fortyEightAT_12379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62124902789) ^ 31062451394 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 62124902789) ^ 4778838676 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 62124902789) ^ 603154396 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 62124902789) ^ 66301924 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 62124902789) ^ 5018572 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_76085543257 : Nat.Prime 76085543257 := by
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_2221
      · exact prime_fortyEightAT_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76085543257) ^ 38042771628 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 25361847752 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 34257336 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 53304 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_96875243347 : Nat.Prime 96875243347 := by
  apply lucas_primality 96875243347 (3 : ZMod 96875243347)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (100284931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (100284931, 1)] : List FactorBlock).map factorBlockValue).prod) = 96875243347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_100284931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96875243347) ^ 48437621673 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 96875243347) ^ 32291747782 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 96875243347) ^ 13839320478 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 96875243347) ^ 4211967102 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 96875243347) ^ 966 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_98987344441 : Nat.Prime 98987344441 := by
  apply lucas_primality 98987344441 (7 : ZMod 98987344441)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (79, 1), (1429, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (79, 1), (1429, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) = 98987344441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_79
      · exact prime_fortyEightAT_1429
      · exact prime_fortyEightAT_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 98987344441) ^ 49493672220 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 32995781480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 19797468888 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 1253004360 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 69270360 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 13546920 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_111069470587 : Nat.Prime 111069470587 := by
  apply lucas_primality 111069470587 (11 : ZMod 111069470587)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod) = 111069470587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_277
      · exact prime_fortyEightAT_66828803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 111069470587) ^ 55534735293 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 37023156862 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 400972818 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 1662 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_124249805579 : Nat.Prime 124249805579 := by
  apply lucas_primality 124249805579 (2 : ZMod 124249805579)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (62124902789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (62124902789, 1)] : List FactorBlock).map factorBlockValue).prod) = 124249805579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_62124902789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 124249805579) ^ 62124902789 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 124249805579) ^ 2 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_132501777739 : Nat.Prime 132501777739 := by
  apply lucas_primality 132501777739 (3 : ZMod 132501777739)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 132501777739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_8747
      · exact prime_fortyEightAT_229519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132501777739) ^ 66250888869 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 44167259246 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 12045616158 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 15148254 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 577302 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_158810207911 : Nat.Prime 158810207911 := by
  apply lucas_primality 158810207911 (6 : ZMod 158810207911)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (113, 1), (2671, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (113, 1), (2671, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) = 158810207911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_113
      · exact prime_fortyEightAT_2671
      · exact prime_fortyEightAT_17539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 158810207911) ^ 79405103955 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 158810207911) ^ 52936735970 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 158810207911) ^ 31762041582 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 158810207911) ^ 1405400070 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 158810207911) ^ 59457210 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 158810207911) ^ 9054690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_159097227851 : Nat.Prime 159097227851 := by
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159097227851) ^ 79548613925 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 31819445570 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 14463384350 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_267332166961 : Nat.Prime 267332166961 := by
  apply lucas_primality 267332166961 (11 : ZMod 267332166961)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1113884029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1113884029, 1)] : List FactorBlock).map factorBlockValue).prod) = 267332166961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_1113884029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 267332166961) ^ 133666083480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 267332166961) ^ 89110722320 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 267332166961) ^ 53466433392 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 267332166961) ^ 240 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_149
      · exact prime_fortyEightAT_1429
      · exact prime_fortyEightAT_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_300822435161 : Nat.Prime 300822435161 := by
  apply lucas_primality 300822435161 (7 : ZMod 300822435161)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (1223, 1), (473021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (1223, 1), (473021, 1)] : List FactorBlock).map factorBlockValue).prod) = 300822435161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_1223
      · exact prime_fortyEightAT_473021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 300822435161) ^ 150411217580 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 300822435161) ^ 60164487032 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 300822435161) ^ 23140187320 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 300822435161) ^ 245970920 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 300822435161) ^ 635960 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_378462185951 : Nat.Prime 378462185951 := by
  apply lucas_primality 378462185951 (11 : ZMod 378462185951)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (307, 1), (1071979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (307, 1), (1071979, 1)] : List FactorBlock).map factorBlockValue).prod) = 378462185951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_307
      · exact prime_fortyEightAT_1071979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 378462185951) ^ 189231092975 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 378462185951) ^ 75692437190 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 378462185951) ^ 16454877650 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 378462185951) ^ 1232775850 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 378462185951) ^ 353050 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_418833512323 : Nat.Prime 418833512323 := by
  apply lucas_primality 418833512323 (7 : ZMod 418833512323)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (47, 1), (47910491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (47, 1), (47910491, 1)] : List FactorBlock).map factorBlockValue).prod) = 418833512323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_47910491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 418833512323) ^ 209416756161 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 418833512323) ^ 139611170774 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 418833512323) ^ 13510758462 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 418833512323) ^ 8911351326 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 418833512323) ^ 8742 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_397
      · exact prime_fortyEightAT_2531
      · exact prime_fortyEightAT_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_568606649021 : Nat.Prime 568606649021 := by
  apply lucas_primality 568606649021 (2 : ZMod 568606649021)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (3067, 1), (174901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (3067, 1), (174901, 1)] : List FactorBlock).map factorBlockValue).prod) = 568606649021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_3067
      · exact prime_fortyEightAT_174901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 568606649021) ^ 284303324510 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 568606649021) ^ 113721329804 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 568606649021) ^ 10728427340 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 568606649021) ^ 185395060 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 568606649021) ^ 3251020 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1272241326337 : Nat.Prime 1272241326337 := by
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1272241326337) ^ 636120663168 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 424080442112 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 768 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_35279
      · exact prime_fortyEightAT_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1662864904867 : Nat.Prime 1662864904867 := by
  apply lucas_primality 1662864904867 (2 : ZMod 1662864904867)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (25194922801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (25194922801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1662864904867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_25194922801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1662864904867) ^ 831432452433 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662864904867) ^ 554288301622 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662864904867) ^ 151169536806 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662864904867) ^ 66 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1716071714267 : Nat.Prime 1716071714267 := by
  apply lucas_primality 1716071714267 (2 : ZMod 1716071714267)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (9428965463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (9428965463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1716071714267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_9428965463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1716071714267) ^ 858035857133 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 245153102038 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 132005516482 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 182 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1744009161931 : Nat.Prime 1744009161931 := by
  apply lucas_primality 1744009161931 (3 : ZMod 1744009161931)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (61, 1), (45381451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (61, 1), (45381451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1744009161931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_45381451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1744009161931) ^ 872004580965 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1744009161931) ^ 581336387310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1744009161931) ^ 348801832386 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1744009161931) ^ 249144165990 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1744009161931) ^ 28590314130 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1744009161931) ^ 38430 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1804934610967 : Nat.Prime 1804934610967 := by
  apply lucas_primality 1804934610967 (3 : ZMod 1804934610967)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (300822435161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (300822435161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1804934610967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_300822435161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1804934610967) ^ 902467305483 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1804934610967) ^ 601644870322 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1804934610967) ^ 6 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1814437336489 : Nat.Prime 1814437336489 := by
  apply lucas_primality 1814437336489 (11 : ZMod 1814437336489)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (10800222241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (10800222241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1814437336489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_10800222241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1814437336489) ^ 907218668244 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 604812445496 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 259205333784 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 168 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_457
      · exact prime_fortyEightAT_1433
      · exact prime_fortyEightAT_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1982473007243 : Nat.Prime 1982473007243 := by
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1982473007243) ^ 991236503621 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 283210429606 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 152497923634 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 182 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2134359662741 : Nat.Prime 2134359662741 := by
  apply lucas_primality 2134359662741 (2 : ZMod 2134359662741)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (263, 1), (13992131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (263, 1), (13992131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2134359662741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_263
      · exact prime_fortyEightAT_13992131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2134359662741) ^ 1067179831370 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134359662741) ^ 426871932548 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134359662741) ^ 73598609060 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134359662741) ^ 8115435980 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134359662741) ^ 152540 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2159986538959 : Nat.Prime 2159986538959 := by
  apply lucas_primality 2159986538959 (6 : ZMod 2159986538959)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61627, 1), (5841559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61627, 1), (5841559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2159986538959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_61627
      · exact prime_fortyEightAT_5841559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2159986538959) ^ 1079993269479 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 719995512986 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 35049354 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 369762 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2329141311671 : Nat.Prime 2329141311671 := by
  apply lucas_primality 2329141311671 (11 : ZMod 2329141311671)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329141311671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_107
      · exact prime_fortyEightAT_5413
      · exact prime_fortyEightAT_402137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2329141311671) ^ 1164570655835 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 465828262334 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 21767675810 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 430286590 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 5791910 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2853675812231 : Nat.Prime 2853675812231 := by
  apply lucas_primality 2853675812231 (23 : ZMod 2853675812231)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (2770559041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (2770559041, 1)] : List FactorBlock).map factorBlockValue).prod) = 2853675812231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_103
      · exact prime_fortyEightAT_2770559041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 2853675812231) ^ 1426837906115 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 2853675812231) ^ 570735162446 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 2853675812231) ^ 27705590410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (23 : ZMod 2853675812231) ^ 1030 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3926359426523 : Nat.Prime 3926359426523 := by
  apply lucas_primality 3926359426523 (2 : ZMod 3926359426523)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (20551, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (20551, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod) = 3926359426523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_20551
      · exact prime_fortyEightAT_319489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3926359426523) ^ 1963179713261 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 302027648194 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 170711279414 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 191054422 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 12289498 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_4287731098507 : Nat.Prime 4287731098507 := by
  apply lucas_primality 4287731098507 (2 : ZMod 4287731098507)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287731098507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_167
      · exact prime_fortyEightAT_70150373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4287731098507) ^ 2143865549253 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 1429243699502 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 70290673746 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 25675036518 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 61122 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_4491424785217 : Nat.Prime 4491424785217 := by
  apply lucas_primality 4491424785217 (7 : ZMod 4491424785217)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4491424785217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_441374291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4491424785217) ^ 2245712392608 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 1497141595072 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 84743863872 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 10176 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_4658282623343 : Nat.Prime 4658282623343 := by
  apply lucas_primality 4658282623343 (5 : ZMod 4658282623343)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658282623343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_2329141311671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4658282623343) ^ 2329141311671 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 4658282623343) ^ 2 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_5934672374047 : Nat.Prime 5934672374047 := by
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934672374047) ^ 2967336187023 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 1978224124682 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 456513259542 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 78 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6442029294047 : Nat.Prime 6442029294047 := by
  apply lucas_primality 6442029294047 (5 : ZMod 6442029294047)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod) = 6442029294047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_111069470587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6442029294047) ^ 3221014647023 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 222138941174 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 58 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8327775513901 : Nat.Prime 8327775513901 := by
  apply lucas_primality 8327775513901 (6 : ZMod 8327775513901)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (107, 1), (259432259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (107, 1), (259432259, 1)] : List FactorBlock).map factorBlockValue).prod) = 8327775513901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_107
      · exact prime_fortyEightAT_259432259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8327775513901) ^ 4163887756950 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 8327775513901) ^ 2775925171300 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 8327775513901) ^ 1665555102780 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 8327775513901) ^ 77829677700 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 8327775513901) ^ 32100 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8402550447737 : Nat.Prime 8402550447737 := by
  apply lucas_primality 8402550447737 (3 : ZMod 8402550447737)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) = 8402550447737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_381761
      · exact prime_fortyEightAT_2751247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8402550447737) ^ 4201275223868 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 22009976 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 3054088 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9977189429203 : Nat.Prime 9977189429203 := by
  apply lucas_primality 9977189429203 (2 : ZMod 9977189429203)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1662864904867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1662864904867, 1)] : List FactorBlock).map factorBlockValue).prod) = 9977189429203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_1662864904867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9977189429203) ^ 4988594714601 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9977189429203) ^ 3325729809734 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9977189429203) ^ 6 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_11012157741281 : Nat.Prime 11012157741281 := by
  apply lucas_primality 11012157741281 (3 : ZMod 11012157741281)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) = 11012157741281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_137
      · exact prime_fortyEightAT_16205789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11012157741281) ^ 5506078870640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 2202431548256 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 355230894880 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 80380713440 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 679520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_11680677399577 : Nat.Prime 11680677399577 := by
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_79
      · exact prime_fortyEightAT_397
      · exact prime_fortyEightAT_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11680677399577) ^ 5840338699788 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 3893559133192 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 507855539112 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 147856675944 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 29422361208 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 17312376 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_12550654586551 : Nat.Prime 12550654586551 := by
  apply lucas_primality 12550654586551 (6 : ZMod 12550654586551)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) = 12550654586551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_66553
      · exact prime_fortyEightAT_1257209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12550654586551) ^ 6275327293275 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 4183551528850 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 2510130917310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 188581350 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 9982950 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_13424731660273 : Nat.Prime 13424731660273 := by
  apply lucas_primality 13424731660273 (5 : ZMod 13424731660273)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) = 13424731660273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_379
      · exact prime_fortyEightAT_907
      · exact prime_fortyEightAT_813613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13424731660273) ^ 6712365830136 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 4474910553424 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 35421455568 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 14801247696 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 16500144 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_13443454509487 : Nat.Prime 13443454509487 := by
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_293
      · exact prime_fortyEightAT_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13443454509487) ^ 6721727254743 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 4481151503162 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 45882097302 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 1758 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_16652980983983 : Nat.Prime 16652980983983 := by
  apply lucas_primality 16652980983983 (5 : ZMod 16652980983983)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (61, 1), (475609213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (61, 1), (475609213, 1)] : List FactorBlock).map factorBlockValue).prod) = 16652980983983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_475609213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16652980983983) ^ 8326490491991 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 16652980983983) ^ 2378997283426 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 16652980983983) ^ 406170267902 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 16652980983983) ^ 272999688262 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 16652980983983) ^ 35014 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_20563414774369 : Nat.Prime 20563414774369 := by
  apply lucas_primality 20563414774369 (17 : ZMod 20563414774369)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (173, 1), (1238163221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (173, 1), (1238163221, 1)] : List FactorBlock).map factorBlockValue).prod) = 20563414774369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_173
      · exact prime_fortyEightAT_1238163221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 20563414774369) ^ 10281707387184 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 6854471591456 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 118863669216 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 16608 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_26484563173451 : Nat.Prime 26484563173451 := by
  apply lucas_primality 26484563173451 (2 : ZMod 26484563173451)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (41, 1), (679963111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (41, 1), (679963111, 1)] : List FactorBlock).map factorBlockValue).prod) = 26484563173451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_679963111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26484563173451) ^ 13242281586725 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26484563173451) ^ 5296912634690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26484563173451) ^ 1393924377550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26484563173451) ^ 645964955450 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 26484563173451) ^ 38950 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_29358487194529 : Nat.Prime 29358487194529 := by
  apply lucas_primality 29358487194529 (7 : ZMod 29358487194529)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (44351, 1), (6895393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (44351, 1), (6895393, 1)] : List FactorBlock).map factorBlockValue).prod) = 29358487194529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_44351
      · exact prime_fortyEightAT_6895393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29358487194529) ^ 14679243597264 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 9786162398176 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 661957728 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 4257696 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_45820001621089 : Nat.Prime 45820001621089 := by
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 45820001621089) ^ 22910000810544 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 15273333873696 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 288 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_53388987237871 : Nat.Prime 53388987237871 := by
  apply lucas_primality 53388987237871 (15 : ZMod 53388987237871)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (131367307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (131367307, 1)] : List FactorBlock).map factorBlockValue).prod) = 53388987237871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_131367307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 53388987237871) ^ 26694493618935 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 17796329079290 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 10677797447574 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 2809946696730 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 2321260314690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 1722225394770 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 406410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_89
      · exact prime_fortyEightAT_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_64296733024847 : Nat.Prime 64296733024847 := by
  apply lucas_primality 64296733024847 (5 : ZMod 64296733024847)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (61, 1), (1836314989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (61, 1), (1836314989, 1)] : List FactorBlock).map factorBlockValue).prod) = 64296733024847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_1836314989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64296733024847) ^ 32148366512423 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 64296733024847) ^ 9185247574978 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 64296733024847) ^ 1568213000606 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 64296733024847) ^ 1054044803686 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 64296733024847) ^ 35014 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_74050722409721 : Nat.Prime 74050722409721 := by
  apply lucas_primality 74050722409721 (6 : ZMod 74050722409721)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) = 74050722409721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_15131
      · exact prime_fortyEightAT_17478479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74050722409721) ^ 37025361204860 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 14810144481944 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 10578674629960 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4893974120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4236680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_77333671361899 : Nat.Prime 77333671361899 := by
  apply lucas_primality 77333671361899 (2 : ZMod 77333671361899)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (353, 1), (691, 1), (2516201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (353, 1), (691, 1), (2516201, 1)] : List FactorBlock).map factorBlockValue).prod) = 77333671361899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_353
      · exact prime_fortyEightAT_691
      · exact prime_fortyEightAT_2516201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77333671361899) ^ 38666835680949 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 77333671361899) ^ 25777890453966 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 77333671361899) ^ 11047667337414 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 77333671361899) ^ 219075556266 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 77333671361899) ^ 111915588078 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 77333671361899) ^ 30734298 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_128096483851537 : Nat.Prime 128096483851537 := by
  apply lucas_primality 128096483851537 (10 : ZMod 128096483851537)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) = 128096483851537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_499
      · exact prime_fortyEightAT_647
      · exact prime_fortyEightAT_8265919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 128096483851537) ^ 64048241925768 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 42698827950512 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 256706380464 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 197985291888 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 15496944 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_167832428999197 : Nat.Prime 167832428999197 := by
  apply lucas_primality 167832428999197 (2 : ZMod 167832428999197)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) = 167832428999197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_73
      · exact prime_fortyEightAT_14737656217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167832428999197) ^ 83916214499598 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 55944142999732 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 12910186846092 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 2299074369852 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 11388 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_170545391855011 : Nat.Prime 170545391855011 := by
  apply lucas_primality 170545391855011 (2 : ZMod 170545391855011)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod) = 170545391855011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_2207
      · exact prime_fortyEightAT_5400053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170545391855011) ^ 85272695927505 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 56848463951670 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 34109078371002 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 3217837582170 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 77274758430 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 31582170 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_211876505387609 : Nat.Prime 211876505387609 := by
  apply lucas_primality 211876505387609 (3 : ZMod 211876505387609)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (26484563173451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (26484563173451, 1)] : List FactorBlock).map factorBlockValue).prod) = 211876505387609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_26484563173451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 211876505387609) ^ 105938252693804 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 211876505387609) ^ 8 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_247566324202231 : Nat.Prime 247566324202231 := by
  apply lucas_primality 247566324202231 (3 : ZMod 247566324202231)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17573, 1), (42690547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17573, 1), (42690547, 1)] : List FactorBlock).map factorBlockValue).prod) = 247566324202231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_17573
      · exact prime_fortyEightAT_42690547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 247566324202231) ^ 123783162101115 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247566324202231) ^ 82522108067410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247566324202231) ^ 49513264840446 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247566324202231) ^ 22506029472930 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247566324202231) ^ 14087880510 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247566324202231) ^ 5799090 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_260391878854403 : Nat.Prime 260391878854403 := by
  apply lucas_primality 260391878854403 (2 : ZMod 260391878854403)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (2134359662741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (2134359662741, 1)] : List FactorBlock).map factorBlockValue).prod) = 260391878854403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_2134359662741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 260391878854403) ^ 130195939427201 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 260391878854403) ^ 4268719325482 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 260391878854403) ^ 122 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_263805968283449 : Nat.Prime 263805968283449 := by
  apply lucas_primality 263805968283449 (3 : ZMod 263805968283449)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (317, 1), (587, 1), (7704943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (317, 1), (587, 1), (7704943, 1)] : List FactorBlock).map factorBlockValue).prod) = 263805968283449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_317
      · exact prime_fortyEightAT_587
      · exact prime_fortyEightAT_7704943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 263805968283449) ^ 131902984141724 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 11469824707976 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 832195483544 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 449413915304 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 34238536 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_284731330549429 : Nat.Prime 284731330549429 := by
  apply lucas_primality 284731330549429 (2 : ZMod 284731330549429)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) = 284731330549429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_67
      · exact prime_fortyEightAT_4441
      · exact prime_fortyEightAT_1265779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 284731330549429) ^ 142365665274714 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 94910443516476 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 40675904364204 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 4249721351484 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 64114237908 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 224945532 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_289817799176999 : Nat.Prime 289817799176999 := by
  apply lucas_primality 289817799176999 (7 : ZMod 289817799176999)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) = 289817799176999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_439
      · exact prime_fortyEightAT_5411288681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 289817799176999) ^ 144908899588499 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 4751111461918 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 660177219082 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 53558 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_399161867612743 : Nat.Prime 399161867612743 := by
  apply lucas_primality 399161867612743 (5 : ZMod 399161867612743)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (568606649021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (568606649021, 1)] : List FactorBlock).map factorBlockValue).prod) = 399161867612743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_568606649021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 399161867612743) ^ 199580933806371 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 399161867612743) ^ 133053955870914 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 399161867612743) ^ 30704759047134 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 399161867612743) ^ 702 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_416726749916363 : Nat.Prime 416726749916363 := by
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_4787
      · exact prime_fortyEightAT_8839
      · exact prime_fortyEightAT_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416726749916363) ^ 208363374958181 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 87053843726 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 47146368358 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 84624586 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_440457562723103 : Nat.Prime 440457562723103 := by
  apply lucas_primality 440457562723103 (5 : ZMod 440457562723103)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod) = 440457562723103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_14081
      · exact prime_fortyEightAT_539315099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 440457562723103) ^ 220228781361551 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 15188191818038 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 31280275742 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 816698 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_446803687100569 : Nat.Prime 446803687100569 := by
  apply lucas_primality 446803687100569 (11 : ZMod 446803687100569)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (139, 1), (13121, 1), (1458229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (139, 1), (13121, 1), (1458229, 1)] : List FactorBlock).map factorBlockValue).prod) = 446803687100569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_139
      · exact prime_fortyEightAT_13121
      · exact prime_fortyEightAT_1458229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 446803687100569) ^ 223401843550284 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 148934562366856 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 63829098157224 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 3214415015112 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 34052563608 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 306401592 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_522414067849459 : Nat.Prime 522414067849459 := by
  apply lucas_primality 522414067849459 (2 : ZMod 522414067849459)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) = 522414067849459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_71
      · exact prime_fortyEightAT_20785154287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 522414067849459) ^ 261207033924729 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 174138022616486 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 8854475726262 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 7357944617598 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 25134 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_906824704194671 : Nat.Prime 906824704194671 := by
  apply lucas_primality 906824704194671 (11 : ZMod 906824704194671)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (773, 1), (6900728287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (773, 1), (6900728287, 1)] : List FactorBlock).map factorBlockValue).prod) = 906824704194671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_773
      · exact prime_fortyEightAT_6900728287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 906824704194671) ^ 453412352097335 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 906824704194671) ^ 181364940838934 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 906824704194671) ^ 53342629658510 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 906824704194671) ^ 1173123808790 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 906824704194671) ^ 131410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1426018778793047 : Nat.Prime 1426018778793047 := by
  apply lucas_primality 1426018778793047 (5 : ZMod 1426018778793047)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426018778793047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11867
      · exact prime_fortyEightAT_60083373169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1426018778793047) ^ 713009389396523 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 120166746338 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 23734 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1802764560956033 : Nat.Prime 1802764560956033 := by
  apply lucas_primality 1802764560956033 (3 : ZMod 1802764560956033)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (157, 1), (39511, 1), (2270447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (157, 1), (39511, 1), (2270447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1802764560956033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_157
      · exact prime_fortyEightAT_39511
      · exact prime_fortyEightAT_2270447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1802764560956033) ^ 901382280478016 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 11482576821376 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 45626902912 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 794013056 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2921124806083031 : Nat.Prime 2921124806083031 := by
  apply lucas_primality 2921124806083031 (7 : ZMod 2921124806083031)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (41, 1), (15137, 1), (16230371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (41, 1), (15137, 1), (16230371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2921124806083031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_15137
      · exact prime_fortyEightAT_16230371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2921124806083031) ^ 1460562403041515 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 2921124806083031) ^ 584224961216606 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 2921124806083031) ^ 100728441589070 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 2921124806083031) ^ 71246946489830 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 2921124806083031) ^ 192979111190 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 2921124806083031) ^ 179978930 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_4243096546919081 : Nat.Prime 4243096546919081 := by
  apply lucas_primality 4243096546919081 (3 : ZMod 4243096546919081)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod) = 4243096546919081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_4817
      · exact prime_fortyEightAT_710369951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4243096546919081) ^ 2121548273459540 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 848619309383816 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 136874082158680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 880858739240 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 5973080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_7254597633557369 : Nat.Prime 7254597633557369 := by
  apply lucas_primality 7254597633557369 (3 : ZMod 7254597633557369)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (906824704194671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (906824704194671, 1)] : List FactorBlock).map factorBlockValue).prod) = 7254597633557369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_906824704194671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7254597633557369) ^ 3627298816778684 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 7254597633557369) ^ 8 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9866893336187777 : Nat.Prime 9866893336187777 := by
  apply lucas_primality 9866893336187777 (3 : ZMod 9866893336187777)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866893336187777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11012157741281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9866893336187777) ^ 4933446668093888 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 1409556190883968 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 896 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_10936458911884927 : Nat.Prime 10936458911884927 := by
  apply lucas_primality 10936458911884927 (5 : ZMod 10936458911884927)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (260391878854403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (260391878854403, 1)] : List FactorBlock).map factorBlockValue).prod) = 10936458911884927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_260391878854403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10936458911884927) ^ 5468229455942463 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 10936458911884927) ^ 3645486303961642 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 10936458911884927) ^ 1562351273126418 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 10936458911884927) ^ 42 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_81047
      · exact prime_fortyEightAT_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_12344096848147619 : Nat.Prime 12344096848147619 := by
  apply lucas_primality 12344096848147619 (2 : ZMod 12344096848147619)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3539, 1), (1744009161931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3539, 1), (1744009161931, 1)] : List FactorBlock).map factorBlockValue).prod) = 12344096848147619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3539
      · exact prime_fortyEightAT_1744009161931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12344096848147619) ^ 6172048424073809 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 12344096848147619) ^ 3488018323862 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 12344096848147619) ^ 7078 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_384973
      · exact prime_fortyEightAT_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_71347522561263737 : Nat.Prime 71347522561263737 := by
  apply lucas_primality 71347522561263737 (3 : ZMod 71347522561263737)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) = 71347522561263737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_24581699
      · exact prime_fortyEightAT_362808133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71347522561263737) ^ 35673761280631868 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 2902465064 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 196653592 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_80581054769871263 : Nat.Prime 80581054769871263 := by
  apply lucas_primality 80581054769871263 (5 : ZMod 80581054769871263)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (61, 1), (83, 1), (418833512323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (61, 1), (83, 1), (418833512323, 1)] : List FactorBlock).map factorBlockValue).prod) = 80581054769871263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_83
      · exact prime_fortyEightAT_418833512323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 80581054769871263) ^ 40290527384935631 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 80581054769871263) ^ 4241108145782698 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 80581054769871263) ^ 1321000897866742 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 80581054769871263) ^ 970856081564714 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 80581054769871263) ^ 192394 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_85512338798115589 : Nat.Prime 85512338798115589 := by
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_71
      · exact prime_fortyEightAT_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85512338798115589) ^ 42756169399057794 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 28504112932705196 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1449361674544332 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1204399138001628 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 3569028 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_95736107307805897 : Nat.Prime 95736107307805897 := by
  apply lucas_primality 95736107307805897 (5 : ZMod 95736107307805897)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (479, 1), (8327775513901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (479, 1), (8327775513901, 1)] : List FactorBlock).map factorBlockValue).prod) = 95736107307805897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_479
      · exact prime_fortyEightAT_8327775513901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95736107307805897) ^ 47868053653902948 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 95736107307805897) ^ 31912035769268632 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 95736107307805897) ^ 199866612333624 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 95736107307805897) ^ 11496 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_145091952671147381 : Nat.Prime 145091952671147381 := by
  apply lucas_primality 145091952671147381 (2 : ZMod 145091952671147381)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7254597633557369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7254597633557369, 1)] : List FactorBlock).map factorBlockValue).prod) = 145091952671147381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7254597633557369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 145091952671147381) ^ 72545976335573690 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 145091952671147381) ^ 29018390534229476 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 145091952671147381) ^ 20 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_161036169666815281 : Nat.Prime 161036169666815281 := by
  apply lucas_primality 161036169666815281 (13 : ZMod 161036169666815281)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (17, 1), (23, 1), (1716071714267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (17, 1), (23, 1), (1716071714267, 1)] : List FactorBlock).map factorBlockValue).prod) = 161036169666815281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_1716071714267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 161036169666815281) ^ 80518084833407640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 53678723222271760 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 32207233933363056 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 9472715862753840 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 7001572594209360 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 93840 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_161449252589470789 : Nat.Prime 161449252589470789 := by
  apply lucas_primality 161449252589470789 (7 : ZMod 161449252589470789)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (263805968283449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (263805968283449, 1)] : List FactorBlock).map factorBlockValue).prod) = 161449252589470789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_263805968283449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 161449252589470789) ^ 80724626294735394 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 53816417529823596 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 9497014858204164 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 612 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_403792693884455891 : Nat.Prime 403792693884455891 := by
  apply lucas_primality 403792693884455891 (2 : ZMod 403792693884455891)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 2), (5087, 1), (3141170261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 2), (5087, 1), (3141170261, 1)] : List FactorBlock).map factorBlockValue).prod) = 403792693884455891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_5087
      · exact prime_fortyEightAT_3141170261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 403792693884455891) ^ 201896346942227945 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 403792693884455891) ^ 80758538776891178 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 403792693884455891) ^ 57684670554922270 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 403792693884455891) ^ 21252247046550310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 403792693884455891) ^ 79377372495470 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 403792693884455891) ^ 128548490 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_61717
      · exact prime_fortyEightAT_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_649421588852263219 : Nat.Prime 649421588852263219 := by
  apply lucas_primality 649421588852263219 (2 : ZMod 649421588852263219)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (769, 1), (5669, 1), (40902889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (769, 1), (5669, 1), (40902889, 1)] : List FactorBlock).map factorBlockValue).prod) = 649421588852263219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_607
      · exact prime_fortyEightAT_769
      · exact prime_fortyEightAT_5669
      · exact prime_fortyEightAT_40902889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 649421588852263219) ^ 324710794426131609 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 649421588852263219) ^ 216473862950754406 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 649421588852263219) ^ 1069887296296974 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 649421588852263219) ^ 844501415932722 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 649421588852263219) ^ 114556639416522 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 649421588852263219) ^ 15877156962 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_710602504382600099 : Nat.Prime 710602504382600099 := by
  apply lucas_primality 710602504382600099 (2 : ZMod 710602504382600099)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) = 710602504382600099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_73
      · exact prime_fortyEightAT_167832428999197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 710602504382600099) ^ 355301252191300049 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 24503534633882762 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 9734280881953426 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 4234 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_795919661150545033 : Nat.Prime 795919661150545033 := by
  apply lucas_primality 795919661150545033 (5 : ZMod 795919661150545033)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3307, 1), (5231, 1), (1917074879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3307, 1), (5231, 1), (1917074879, 1)] : List FactorBlock).map factorBlockValue).prod) = 795919661150545033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_3307
      · exact prime_fortyEightAT_5231
      · exact prime_fortyEightAT_1917074879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 795919661150545033) ^ 397959830575272516 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 795919661150545033) ^ 265306553716848344 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 795919661150545033) ^ 240677248609176 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 795919661150545033) ^ 152154398996472 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 795919661150545033) ^ 415174008 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_978570257152699693 : Nat.Prime 978570257152699693 := by
  apply lucas_primality 978570257152699693 (5 : ZMod 978570257152699693)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (29, 1), (21247, 1), (1131173671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (29, 1), (21247, 1), (1131173671, 1)] : List FactorBlock).map factorBlockValue).prod) = 978570257152699693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_21247
      · exact prime_fortyEightAT_1131173671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 978570257152699693) ^ 489285128576349846 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 326190085717566564 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 75274635165592284 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 33743801970782748 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 46056867188436 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 865092852 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1755892682371176143 : Nat.Prime 1755892682371176143 := by
  apply lucas_primality 1755892682371176143 (7 : ZMod 1755892682371176143)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (487, 1), (1802764560956033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (487, 1), (1802764560956033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1755892682371176143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_487
      · exact prime_fortyEightAT_1802764560956033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1755892682371176143) ^ 877946341185588071 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 1755892682371176143) ^ 3605529121912066 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 1755892682371176143) ^ 974 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_5160635946694138763 : Nat.Prime 5160635946694138763 := by
  apply lucas_primality 5160635946694138763 (2 : ZMod 5160635946694138763)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (613, 1), (91757, 1), (45874732741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (613, 1), (91757, 1), (45874732741, 1)] : List FactorBlock).map factorBlockValue).prod) = 5160635946694138763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_613
      · exact prime_fortyEightAT_91757
      · exact prime_fortyEightAT_45874732741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5160635946694138763) ^ 2580317973347069381 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160635946694138763) ^ 8418655704231874 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160635946694138763) ^ 56242422340466 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160635946694138763) ^ 112494082 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6634509058759861109 : Nat.Prime 6634509058759861109 := by
  apply lucas_primality 6634509058759861109 (2 : ZMod 6634509058759861109)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) = 6634509058759861109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_97
      · exact prime_fortyEightAT_289817799176999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6634509058759861109) ^ 3317254529379930554 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 112449306080675612 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 68397000605771764 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 22892 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_439
      · exact prime_fortyEightAT_853
      · exact prime_fortyEightAT_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_15811511862622282211 : Nat.Prime 15811511862622282211 := by
  apply lucas_primality 15811511862622282211 (2 : ZMod 15811511862622282211)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (757, 1), (967, 1), (2159986538959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (757, 1), (967, 1), (2159986538959, 1)] : List FactorBlock).map factorBlockValue).prod) = 15811511862622282211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_757
      · exact prime_fortyEightAT_967
      · exact prime_fortyEightAT_2159986538959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15811511862622282211) ^ 7905755931311141105 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 3162302372524456442 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 20887069831733530 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 16351098099919630 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 7320190 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_20016883181133315649 : Nat.Prime 20016883181133315649 := by
  apply lucas_primality 20016883181133315649 (11 : ZMod 20016883181133315649)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (91823, 1), (378462185951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (91823, 1), (378462185951, 1)] : List FactorBlock).map factorBlockValue).prod) = 20016883181133315649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_91823
      · exact prime_fortyEightAT_378462185951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 20016883181133315649) ^ 10008441590566657824 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 20016883181133315649) ^ 6672294393711105216 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 20016883181133315649) ^ 217994219107776 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (11 : ZMod 20016883181133315649) ^ 52890048 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_28865922088264225807 : Nat.Prime 28865922088264225807 := by
  apply lucas_primality 28865922088264225807 (3 : ZMod 28865922088264225807)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) = 28865922088264225807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_821
      · exact prime_fortyEightAT_9124861
      · exact prime_fortyEightAT_642191821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28865922088264225807) ^ 14432961044132112903 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 9621974029421408602 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 35159466611771286 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 3163436910246 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 44949065286 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_132124709315903817101 : Nat.Prime 132124709315903817101 := by
  apply lucas_primality 132124709315903817101 (2 : ZMod 132124709315903817101)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (169789, 1), (158810207911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (169789, 1), (158810207911, 1)] : List FactorBlock).map factorBlockValue).prod) = 132124709315903817101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_169789
      · exact prime_fortyEightAT_158810207911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 132124709315903817101) ^ 66062354657951908550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 132124709315903817101) ^ 26424941863180763420 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 132124709315903817101) ^ 18874958473700545300 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 132124709315903817101) ^ 778170018763900 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 132124709315903817101) ^ 831966100 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_193386936761767911941 : Nat.Prime 193386936761767911941 := by
  apply lucas_primality 193386936761767911941 (2 : ZMod 193386936761767911941)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (101, 1), (95736107307805897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (101, 1), (95736107307805897, 1)] : List FactorBlock).map factorBlockValue).prod) = 193386936761767911941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_101
      · exact prime_fortyEightAT_95736107307805897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193386936761767911941) ^ 96693468380883955970 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386936761767911941) ^ 38677387352353582388 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386936761767911941) ^ 1914722146156117940 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386936761767911941) ^ 2020 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_199
      · exact prime_fortyEightAT_5449
      · exact prime_fortyEightAT_8089
      · exact prime_fortyEightAT_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_631493781802823888411 : Nat.Prime 631493781802823888411 := by
  apply lucas_primality 631493781802823888411 (2 : ZMod 631493781802823888411)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 2), (257, 1), (13679, 1), (21207925801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 2), (257, 1), (13679, 1), (21207925801, 1)] : List FactorBlock).map factorBlockValue).prod) = 631493781802823888411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_257
      · exact prime_fortyEightAT_13679
      · exact prime_fortyEightAT_21207925801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 631493781802823888411) ^ 315746890901411944205 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 126298756360564777682 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 90213397400403412630 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 57408525618438535310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 2457174248260015130 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 46165200804358790 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 631493781802823888411) ^ 29776310410 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_702451380642795339781 : Nat.Prime 702451380642795339781 := by
  apply lucas_primality 702451380642795339781 (2 : ZMod 702451380642795339781)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod) = 702451380642795339781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_372377
      · exact prime_fortyEightAT_4491424785217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 702451380642795339781) ^ 351225690321397669890 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 234150460214265113260 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 140490276128559067956 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 100350197234685048540 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 1886398409791140 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 156398340 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_941740464079439835397 : Nat.Prime 941740464079439835397 := by
  apply lucas_primality 941740464079439835397 (2 : ZMod 941740464079439835397)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (839, 1), (965551, 1), (96875243347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (839, 1), (965551, 1), (96875243347, 1)] : List FactorBlock).map factorBlockValue).prod) = 941740464079439835397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_839
      · exact prime_fortyEightAT_965551
      · exact prime_fortyEightAT_96875243347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 941740464079439835397) ^ 470870232039719917698 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 941740464079439835397) ^ 313913488026479945132 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 941740464079439835397) ^ 1122455857067270364 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 941740464079439835397) ^ 975339950017596 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 941740464079439835397) ^ 9721167468 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_107
      · exact prime_fortyEightAT_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3435242442213499244627 : Nat.Prime 3435242442213499244627 := by
  apply lucas_primality 3435242442213499244627 (2 : ZMod 3435242442213499244627)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (132124709315903817101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (132124709315903817101, 1)] : List FactorBlock).map factorBlockValue).prod) = 3435242442213499244627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_132124709315903817101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3435242442213499244627) ^ 1717621221106749622313 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3435242442213499244627) ^ 264249418631807634202 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3435242442213499244627) ^ 26 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3790089328897386729757 : Nat.Prime 3790089328897386729757 := by
  apply lucas_primality 3790089328897386729757 (2 : ZMod 3790089328897386729757)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (1567, 1), (2921124806083031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (1567, 1), (2921124806083031, 1)] : List FactorBlock).map factorBlockValue).prod) = 3790089328897386729757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_1567
      · exact prime_fortyEightAT_2921124806083031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3790089328897386729757) ^ 1895044664448693364878 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3790089328897386729757) ^ 1263363109632462243252 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3790089328897386729757) ^ 164786492560755944772 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3790089328897386729757) ^ 2418691339436749668 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 3790089328897386729757) ^ 1297476 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_6595132914986137593109 : Nat.Prime 6595132914986137593109 := by
  apply lucas_primality 6595132914986137593109 (2 : ZMod 6595132914986137593109)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (313, 1), (1755892682371176143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (313, 1), (1755892682371176143, 1)] : List FactorBlock).map factorBlockValue).prod) = 6595132914986137593109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_313
      · exact prime_fortyEightAT_1755892682371176143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6595132914986137593109) ^ 3297566457493068796554 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 2198377638328712531036 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 21070712188454113716 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 3756 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8413993533608191597031 : Nat.Prime 8413993533608191597031 := by
  apply lucas_primality 8413993533608191597031 (39 : ZMod 8413993533608191597031)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (985098929, 1), (19863412949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (985098929, 1), (19863412949, 1)] : List FactorBlock).map factorBlockValue).prod) = 8413993533608191597031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_985098929
      · exact prime_fortyEightAT_19863412949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 8413993533608191597031) ^ 4206996766804095798515 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (39 : ZMod 8413993533608191597031) ^ 1682798706721638319406 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (39 : ZMod 8413993533608191597031) ^ 195674268223446316210 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (39 : ZMod 8413993533608191597031) ^ 8541267568070 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (39 : ZMod 8413993533608191597031) ^ 423592539470 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_8713293684370321798361 : Nat.Prime 8713293684370321798361 := by
  apply lucas_primality 8713293684370321798361 (3 : ZMod 8713293684370321798361)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod) = 8713293684370321798361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_182467
      · exact prime_fortyEightAT_170545391855011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8713293684370321798361) ^ 4356646842185160899180 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1742658736874064359672 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1244756240624331685480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 47752709719403080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 51090760 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_9396985754191469517451 : Nat.Prime 9396985754191469517451 := by
  apply lucas_primality 9396985754191469517451 (2 : ZMod 9396985754191469517451)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod) = 9396985754191469517451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_61
      · exact prime_fortyEightAT_163
      · exact prime_fortyEightAT_503
      · exact prime_fortyEightAT_1976731
      · exact prime_fortyEightAT_2112239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9396985754191469517451) ^ 4698492877095734758725 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 3132328584730489839150 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 1879397150838293903490 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 154048946790024090450 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 57650219350867911150 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 18681880227020814150 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4753800974533950 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4448826933974550 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_15160357315589546919029 : Nat.Prime 15160357315589546919029 := by
  apply lucas_primality 15160357315589546919029 (2 : ZMod 15160357315589546919029)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3790089328897386729757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3790089328897386729757, 1)] : List FactorBlock).map factorBlockValue).prod) = 15160357315589546919029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3790089328897386729757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 15160357315589546919029) ^ 7580178657794773459514 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 15160357315589546919029) ^ 4 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_24979030571864733112961 : Nat.Prime 24979030571864733112961 := by
  apply lucas_primality 24979030571864733112961 (3 : ZMod 24979030571864733112961)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (269, 1), (145091952671147381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (269, 1), (145091952671147381, 1)] : List FactorBlock).map factorBlockValue).prod) = 24979030571864733112961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_269
      · exact prime_fortyEightAT_145091952671147381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24979030571864733112961) ^ 12489515285932366556480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 24979030571864733112961) ^ 4995806114372946622592 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 24979030571864733112961) ^ 92858849709534323840 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 24979030571864733112961) ^ 172160 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_32951634369673100648621 : Nat.Prime 32951634369673100648621 := by
  apply lucas_primality 32951634369673100648621 (2 : ZMod 32951634369673100648621)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (643, 1), (897907, 1), (2853675812231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (643, 1), (897907, 1), (2853675812231, 1)] : List FactorBlock).map factorBlockValue).prod) = 32951634369673100648621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_643
      · exact prime_fortyEightAT_897907
      · exact prime_fortyEightAT_2853675812231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32951634369673100648621) ^ 16475817184836550324310 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 32951634369673100648621) ^ 6590326873934620129724 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 32951634369673100648621) ^ 51246709750658010340 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 32951634369673100648621) ^ 36698270945290660 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 32951634369673100648621) ^ 11547084020 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_89316303497550980360303 : Nat.Prime 89316303497550980360303 := by
  apply lucas_primality 89316303497550980360303 (5 : ZMod 89316303497550980360303)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3435242442213499244627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3435242442213499244627, 1)] : List FactorBlock).map factorBlockValue).prod) = 89316303497550980360303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_3435242442213499244627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 89316303497550980360303) ^ 44658151748775490180151 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 89316303497550980360303) ^ 6870484884426998489254 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 89316303497550980360303) ^ 26 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_119840287954131290354387 : Nat.Prime 119840287954131290354387 := by
  apply lucas_primality 119840287954131290354387 (2 : ZMod 119840287954131290354387)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (683, 1), (5160635946694138763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (683, 1), (5160635946694138763, 1)] : List FactorBlock).map factorBlockValue).prod) = 119840287954131290354387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_683
      · exact prime_fortyEightAT_5160635946694138763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119840287954131290354387) ^ 59920143977065645177193 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 119840287954131290354387) ^ 7049428703184193550258 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 119840287954131290354387) ^ 175461622187600717942 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 119840287954131290354387) ^ 23222 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_247262885986263959602913 : Nat.Prime 247262885986263959602913 := by
  apply lucas_primality 247262885986263959602913 (3 : ZMod 247262885986263959602913)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod) = 247262885986263959602913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_702451380642795339781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 247262885986263959602913) ^ 123631442993131979801456 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 22478444180569450872992 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 352 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_3061
      · exact prime_fortyEightAT_61379
      · exact prime_fortyEightAT_382747
      · exact prime_fortyEightAT_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_754618367023955065564019 : Nat.Prime 754618367023955065564019 := by
  apply lucas_primality 754618367023955065564019 (2 : ZMod 754618367023955065564019)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (43, 1), (17581, 1), (2183231, 1), (9939346271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (43, 1), (17581, 1), (2183231, 1), (9939346271, 1)] : List FactorBlock).map factorBlockValue).prod) = 754618367023955065564019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_17581
      · exact prime_fortyEightAT_2183231
      · exact prime_fortyEightAT_9939346271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 754618367023955065564019) ^ 377309183511977532782009 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 32809494218432828937566 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 17549264349394303850326 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 42922380241394406778 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 345642933351512078 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 75922333969358 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_938632965099248562505919 : Nat.Prime 938632965099248562505919 := by
  apply lucas_primality 938632965099248562505919 (7 : ZMod 938632965099248562505919)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) = 938632965099248562505919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3011
      · exact prime_fortyEightAT_15797
      · exact prime_fortyEightAT_9866893336187777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 938632965099248562505919) ^ 469316482549624281252959 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 311734628063516626538 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 59418431670522793094 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 95129534 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_10641067023614376306121387 : Nat.Prime 10641067023614376306121387 := by
  apply lucas_primality 10641067023614376306121387 (2 : ZMod 10641067023614376306121387)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (24979030571864733112961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (24979030571864733112961, 1)] : List FactorBlock).map factorBlockValue).prod) = 10641067023614376306121387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_71
      · exact prime_fortyEightAT_24979030571864733112961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10641067023614376306121387) ^ 5320533511807188153060693 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 10641067023614376306121387) ^ 3547022341204792102040462 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 10641067023614376306121387) ^ 149874183431188398677766 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (2 : ZMod 10641067023614376306121387) ^ 426 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_18947849895470941182152039 : Nat.Prime 18947849895470941182152039 := by
  apply lucas_primality 18947849895470941182152039 (7 : ZMod 18947849895470941182152039)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 2), (71, 1), (3931, 1), (661009, 1), (7467275083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 2), (71, 1), (3931, 1), (661009, 1), (7467275083, 1)] : List FactorBlock).map factorBlockValue).prod) = 18947849895470941182152039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_71
      · exact prime_fortyEightAT_3931
      · exact prime_fortyEightAT_661009
      · exact prime_fortyEightAT_7467275083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18947849895470941182152039) ^ 9473924947735470591076019 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 1457526915036226244780926 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 823819560672649616615306 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 266871125288323115241578 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 4820109360333487962898 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 28665040711202027782 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (7 : ZMod 18947849895470941182152039) ^ 2537451705590386 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_652285177436039871730406401 : Nat.Prime 652285177436039871730406401 := by
  apply lucas_primality 652285177436039871730406401 (87 : ZMod 652285177436039871730406401)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 652285177436039871730406401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (87 : ZMod 652285177436039871730406401) ^ 326142588718019935865203200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 217428392478679957243468800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 130457035487207974346081280 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 93183596776577124532915200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 59298652494185442884582400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 50175782879695374748492800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 38369716319767051278259200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 34330798812423151143705600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 28360225105914777031756800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 21041457336646447475174400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 17629329119892969506227200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15909394571610728578790400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15169422731070694691404800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 13878408030554039824051200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 12307267498793205126988800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 11055680973492201215769600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 10693199630099014290662400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_736997538142019075851238401 : Nat.Prime 736997538142019075851238401 := by
  apply lucas_primality 736997538142019075851238401 (113 : ZMod 736997538142019075851238401)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 736997538142019075851238401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 736997538142019075851238401) ^ 368498769071009537925619200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 245665846047339691950412800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 147399507628403815170247680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 105285362591717010835891200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 56692118318616851988556800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 43352796361295239755955200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 38789344112737846097433600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 32043371223566046776140800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 25413708211793761236249600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 23774114133613518575846400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 19918852382216731779763200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 17975549710780953069542400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 17139477631209745950028800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 15680798683872746294707200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 13905613927207907091532800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 12491483697322357217817600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (113 : ZMod 736997538142019075851238401) ^ 12081926854787197964774400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1031796553398826706191733761 : Nat.Prime 1031796553398826706191733761 := by
  apply lucas_primality 1031796553398826706191733761 (157 : ZMod 1031796553398826706191733761)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1031796553398826706191733761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (157 : ZMod 1031796553398826706191733761) ^ 515898276699413353095866880 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 343932184466275568730577920 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 206359310679765341238346752 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 147399507628403815170247680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 79368965646063592783979520 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 60693914905813335658337280 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 54305081757832984536407040 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 44860719712992465486597120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 35579191496511265730749440 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 33283759787058926006184960 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 27886393335103424491668480 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 25165769595093334297359360 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 23995268683693644330040320 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 21953118157421844812590080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 19467859498091069928145920 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 17488077176251300104944640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (157 : ZMod 1031796553398826706191733761) ^ 16914697596702077150684160 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1621394583912441966872724481 : Nat.Prime 1621394583912441966872724481 := by
  apply lucas_primality 1621394583912441966872724481 (79 : ZMod 1621394583912441966872724481)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1621394583912441966872724481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1621394583912441966872724481) ^ 810697291956220983436362240 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 540464861304147322290908160 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 324278916782488393374544896 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 231627797701777423838960640 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 147399507628403815170247680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 124722660300957074374824960 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 95376151994849527463101440 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 85336557048023261414353920 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 70495416691845302907509760 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 55910158065946274719749120 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 52303051093949740866862080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 43821475240876809915479040 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 39546209363718096752993280 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 37706850788661441090063360 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 34497757104520041848355840 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 30592350639857395601372160 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 27481264134109185879198720 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 1621394583912441966872724481) ^ 26580239080531835522503680 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_1830606788288240930340172801 : Nat.Prime 1830606788288240930340172801 := by
  apply lucas_primality 1830606788288240930340172801 (89 : ZMod 1830606788288240930340172801)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1830606788288240930340172801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 1830606788288240930340172801) ^ 915303394144120465170086400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 610202262762746976780057600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 366121357657648186068034560 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 261515255469748704334310400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 166418798935294630030924800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 140815906791403148487705600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 107682752252249466490598400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 96347725699381101596851200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 79591599490793083927833600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 63124372009939342425523200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 49475859142925430549734400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 44648946055810754398540800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 42572250890424207682329600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 38949080601877466602982400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 34539750722419640195097600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 31027233699800693734579200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (89 : ZMod 1830606788288240930340172801) ^ 30009947348987556235084800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_2467339584214585601762841601 : Nat.Prime 2467339584214585601762841601 := by
  apply lucas_primality 2467339584214585601762841601 (79 : ZMod 2467339584214585601762841601)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2467339584214585601762841601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_17
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 2467339584214585601762841601) ^ 1233669792107292800881420800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 822446528071528533920947200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 493467916842917120352568320 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 352477083459226514537548800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 224303598564962327432985600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 189795352631891200135603200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 145137622600857976574284800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 129859978116557136934886400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 85080675317744331095270400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 79591599490793083927833600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 66684853627421232480076800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 60179014249136234189337600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 57379990330571758180531200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 52496586898182672377932800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 46553577060652558523827200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 41819314986687891555302400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (79 : ZMod 2467339584214585601762841601) ^ 40448189905157141012505600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem prime_fortyEightAT_3338165319819733461208550401 : Nat.Prime 3338165319819733461208550401 := by
  apply lucas_primality 3338165319819733461208550401 (71 : ZMod 3338165319819733461208550401)
  · rw [← fortyEightATFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3338165319819733461208550401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyEightAT_2
      · exact prime_fortyEightAT_3
      · exact prime_fortyEightAT_5
      · exact prime_fortyEightAT_7
      · exact prime_fortyEightAT_11
      · exact prime_fortyEightAT_13
      · exact prime_fortyEightAT_19
      · exact prime_fortyEightAT_23
      · exact prime_fortyEightAT_29
      · exact prime_fortyEightAT_31
      · exact prime_fortyEightAT_37
      · exact prime_fortyEightAT_41
      · exact prime_fortyEightAT_43
      · exact prime_fortyEightAT_47
      · exact prime_fortyEightAT_53
      · exact prime_fortyEightAT_59
      · exact prime_fortyEightAT_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 3338165319819733461208550401) ^ 1669082659909866730604275200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 1112721773273244487069516800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 667633063963946692241710080 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 476880759974247637315507200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 303469574529066678291686400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 256781947678441035477580800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 175692911569459655853081600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 145137622600857976574284800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 115109148959301153834777600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 107682752252249466490598400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 90220684319452255708339200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 81418666337066669785574400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 77631751623714731656012800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 71024794038717733217203200 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 62984251317353461532236800 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 56579073217283617986585600 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide
    · change (71 : ZMod 3338165319819733461208550401) ^ 54724021636389073134566400 ≠ 1
      rw [← fortyEightATFastPow_eq_pow]
      decide

private theorem phi_fortyEightAT_56748810436935468840545356800 : Nat.totient 56748810436935468840545356800 = 7467425686049310690508800000 := by
  rw [← show ((([(2, 10), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_7, prime_fortyEightAT_11, prime_fortyEightAT_13, prime_fortyEightAT_17, prime_fortyEightAT_19, prime_fortyEightAT_23, prime_fortyEightAT_29, prime_fortyEightAT_31, prime_fortyEightAT_37, prime_fortyEightAT_41, prime_fortyEightAT_43, prime_fortyEightAT_47, prime_fortyEightAT_53, prime_fortyEightAT_59, prime_fortyEightAT_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356801 : Nat.totient 56748810436935468840545356801 = 56135519187991545287554007040 := by
  rw [← show ((([(137, 1), (283, 1), (16480507, 1), (73588961, 1), (1206886753, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_137, prime_fortyEightAT_283, prime_fortyEightAT_16480507, prime_fortyEightAT_73588961, prime_fortyEightAT_1206886753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356802 : Nat.totient 56748810436935468840545356802 = 28225848092486214184111416000 := by
  rw [← show ((([(2, 1), (191, 1), (922507631, 1), (161036169666815281, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_191, prime_fortyEightAT_922507631, prime_fortyEightAT_161036169666815281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356803 : Nat.totient 56748810436935468840545356803 = 37832540289869107498358282408 := by
  rw [← show ((([(3, 1), (26620044299, 1), (710602504382600099, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_26620044299, prime_fortyEightAT_710602504382600099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356804 : Nat.totient 56748810436935468840545356804 = 28128625909797388044427269120 := by
  rw [← show ((([(2, 2), (181, 1), (317, 1), (247262885986263959602913, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_181, prime_fortyEightAT_317, prime_fortyEightAT_247262885986263959602913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356805 : Nat.totient 56748810436935468840545356805 = 45323256949966491307707674896 := by
  rw [← show ((([(5, 1), (599, 1), (18947849895470941182152039, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_599, prime_fortyEightAT_18947849895470941182152039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356806 : Nat.totient 56748810436935468840545356806 = 18795777323961156236076393216 := by
  rw [← show ((([(2, 1), (3, 1), (157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_157, prime_fortyEightAT_4315799, prime_fortyEightAT_7041049, prime_fortyEightAT_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356807 : Nat.totient 56748810436935468840545356807 = 48217942340973882053391196512 := by
  rw [← show ((([(7, 1), (139, 1), (653, 1), (89316303497550980360303, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_7, prime_fortyEightAT_139, prime_fortyEightAT_653, prime_fortyEightAT_89316303497550980360303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356808 : Nat.totient 56748810436935468840545356808 = 28374160405918078552743169920 := by
  rw [← show ((([(2, 3), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_115903, prime_fortyEightAT_32244294937, prime_fortyEightAT_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356809 : Nat.totient 56748810436935468840545356809 = 37578421082817063664875294720 := by
  rw [← show ((([(3, 2), (149, 1), (180497, 1), (27902741, 1), (8402550447737, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_149, prime_fortyEightAT_180497, prime_fortyEightAT_27902741, prime_fortyEightAT_8402550447737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356810 : Nat.totient 56748810436935468840545356810 = 22563643268499179843484576000 := by
  rw [← show ((([(2, 1), (5, 1), (173, 1), (4951, 1), (228023, 1), (1805911, 1), (16089506899, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_173, prime_fortyEightAT_4951, prime_fortyEightAT_228023, prime_fortyEightAT_1805911, prime_fortyEightAT_16089506899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356811 : Nat.totient 56748810436935468840545356811 = 51589758205625336998877268000 := by
  rw [← show ((([(11, 2), (742681, 1), (631493781802823888411, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_11, prime_fortyEightAT_742681, prime_fortyEightAT_631493781802823888411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356812 : Nat.totient 56748810436935468840545356812 = 18867038531782032696231936000 := by
  rw [← show ((([(2, 2), (3, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_401, prime_fortyEightAT_11069, prime_fortyEightAT_53269, prime_fortyEightAT_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356813 : Nat.totient 56748810436935468840545356813 = 52383456611379934695074407680 := by
  rw [← show ((([(13, 1), (862819, 1), (18925287739, 1), (267332166961, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_13, prime_fortyEightAT_862819, prime_fortyEightAT_18925287739, prime_fortyEightAT_267332166961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356814 : Nat.totient 56748810436935468840545356814 = 24317472974197316796885191904 := by
  rw [← show ((([(2, 1), (7, 1), (9067, 1), (32143, 1), (3542327, 1), (3926359426523, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_7, prime_fortyEightAT_9067, prime_fortyEightAT_32143, prime_fortyEightAT_3542327, prime_fortyEightAT_3926359426523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356815 : Nat.totient 56748810436935468840545356815 = 29796340362688324612496719872 := by
  rw [← show ((([(3, 1), (5, 1), (67, 1), (1889, 1), (13693, 1), (39926713, 1), (54675980063, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_67, prime_fortyEightAT_1889, prime_fortyEightAT_13693, prime_fortyEightAT_39926713, prime_fortyEightAT_54675980063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356816 : Nat.totient 56748810436935468840545356816 = 28374405217535255914709808800 := by
  rw [← show ((([(2, 4), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_30429025931, prime_fortyEightAT_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356817 : Nat.totient 56748810436935468840545356817 = 53410645117115735379336806400 := by
  rw [← show ((([(17, 1), (3338165319819733461208550401, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_17, prime_fortyEightAT_3338165319819733461208550401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356818 : Nat.totient 56748810436935468840545356818 = 18878663245492027111985259552 := by
  rw [← show ((([(2, 1), (3, 2), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_503, prime_fortyEightAT_15040590709, prime_fortyEightAT_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356819 : Nat.totient 56748810436935468840545356819 = 53759873815071480327816142056 := by
  rw [← show ((([(19, 1), (24923, 1), (119840287954131290354387, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_19, prime_fortyEightAT_24923, prime_fortyEightAT_119840287954131290354387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356820 : Nat.totient 56748810436935468840545356820 = 22699524174770612339482005536 := by
  rw [← show ((([(2, 2), (5, 1), (6442029294047, 1), (440457562723103, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_6442029294047, prime_fortyEightAT_440457562723103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356821 : Nat.totient 56748810436935468840545356821 = 32416628082667648354704384048 := by
  rw [← show ((([(3, 1), (7, 1), (2879, 1), (938632965099248562505919, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_7, prime_fortyEightAT_2879, prime_fortyEightAT_938632965099248562505919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356822 : Nat.totient 56748810436935468840545356822 = 25566562037057670271412582400 := by
  rw [← show ((([(2, 1), (11, 1), (113, 1), (637519, 1), (670673, 1), (53388987237871, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_11, prime_fortyEightAT_113, prime_fortyEightAT_637519, prime_fortyEightAT_670673, prime_fortyEightAT_53388987237871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356823 : Nat.totient 56748810436935468840545356823 = 54281470852720883238782515200 := by
  rw [← show ((([(23, 1), (2467339584214585601762841601, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_23, prime_fortyEightAT_2467339584214585601762841601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356824 : Nat.totient 56748810436935468840545356824 = 18916180150877748968060860416 := by
  rw [← show ((([(2, 3), (3, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_210193, prime_fortyEightAT_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356825 : Nat.totient 56748810436935468840545356825 = 45398880069677702908598949200 := by
  rw [← show ((([(5, 2), (269783, 1), (8413993533608191597031, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_269783, prime_fortyEightAT_8413993533608191597031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356826 : Nat.totient 56748810436935468840545356826 = 26191452796726712525364821760 := by
  rw [← show ((([(2, 1), (13, 1), (175141, 1), (183439, 1), (1934663, 1), (35115478373, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_13, prime_fortyEightAT_175141, prime_fortyEightAT_183439, prime_fortyEightAT_1934663, prime_fortyEightAT_35115478373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356827 : Nat.totient 56748810436935468840545356827 = 36988083132433419540129730560 := by
  rw [← show ((([(3, 3), (83, 1), (97, 1), (13309, 1), (68891, 1), (284731330549429, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_83, prime_fortyEightAT_97, prime_fortyEightAT_13309, prime_fortyEightAT_68891, prime_fortyEightAT_284731330549429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356828 : Nat.totient 56748810436935468840545356828 = 24047478445268565214835731200 := by
  rw [← show ((([(2, 2), (7, 1), (109, 1), (479, 1), (8596663, 1), (20538307, 1), (219857951, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_7, prime_fortyEightAT_109, prime_fortyEightAT_479, prime_fortyEightAT_8596663, prime_fortyEightAT_20538307, prime_fortyEightAT_219857951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356829 : Nat.totient 56748810436935468840545356829 = 54577370438953250408767242240 := by
  rw [← show ((([(29, 1), (257, 1), (39373, 1), (193386936761767911941, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_29, prime_fortyEightAT_257, prime_fortyEightAT_39373, prime_fortyEightAT_193386936761767911941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356830 : Nat.totient 56748810436935468840545356830 = 15132836825899783643358817920 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_85243, prime_fortyEightAT_18480383, prime_fortyEightAT_23255671, prime_fortyEightAT_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356831 : Nat.totient 56748810436935468840545356831 = 54918203648647227910205184000 := by
  rw [← show ((([(31, 1), (1830606788288240930340172801, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_31, prime_fortyEightAT_1830606788288240930340172801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356832 : Nat.totient 56748810436935468840545356832 = 28370652939155871076617400320 := by
  rw [← show ((([(2, 5), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_8233, prime_fortyEightAT_93811, prime_fortyEightAT_8274073, prime_fortyEightAT_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356833 : Nat.totient 56748810436935468840545356833 = 34393218446624726448747555840 := by
  rw [← show ((([(3, 1), (11, 1), (13424731660273, 1), (128096483851537, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_11, prime_fortyEightAT_13424731660273, prime_fortyEightAT_128096483851537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356834 : Nat.totient 56748810436935468840545356834 = 26705322542900743547935064832 := by
  rw [← show ((([(2, 1), (17, 1), (1705633957, 1), (978570257152699693, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_17, prime_fortyEightAT_1705633957, prime_fortyEightAT_978570257152699693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356835 : Nat.totient 56748810436935468840545356835 = 38913470013898607204945387520 := by
  rw [← show ((([(5, 1), (7, 1), (1621394583912441966872724481, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_7, prime_fortyEightAT_1621394583912441966872724481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356836 : Nat.totient 56748810436935468840545356836 = 18916270145645156280181785600 := by
  rw [← show ((([(2, 2), (3, 2), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356837 : Nat.totient 56748810436935468840545356837 = 55215058803060388533977275344 := by
  rw [← show ((([(37, 1), (124249805579, 1), (12344096848147619, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_37, prime_fortyEightAT_124249805579, prime_fortyEightAT_12344096848147619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356838 : Nat.totient 56748810436935468840545356838 = 26867432339520896154341296872 := by
  rw [← show ((([(2, 1), (19, 1), (1979, 1), (754618367023955065564019, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_19, prime_fortyEightAT_1979, prime_fortyEightAT_754618367023955065564019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356839 : Nat.totient 56748810436935468840545356839 = 34917626474501463276546125952 := by
  rw [← show ((([(3, 1), (13, 1), (14347, 1), (15287, 1), (6634509058759861109, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_13, prime_fortyEightAT_14347, prime_fortyEightAT_15287, prime_fortyEightAT_6634509058759861109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356840 : Nat.totient 56748810436935468840545356840 = 22677722319620197357310803968 := by
  rw [← show ((([(2, 3), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_1049, prime_fortyEightAT_139537, prime_fortyEightAT_175593973, prime_fortyEightAT_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356841 : Nat.totient 56748810436935468840545356841 = 55329718558141682345994535680 := by
  rw [← show ((([(41, 1), (1583, 1), (4126759783, 1), (211876505387609, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_41, prime_fortyEightAT_1583, prime_fortyEightAT_4126759783, prime_fortyEightAT_211876505387609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356842 : Nat.totient 56748810436935468840545356842 = 16008706018362235401871405056 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_7, prime_fortyEightAT_79, prime_fortyEightAT_1272241326337, prime_fortyEightAT_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356843 : Nat.totient 56748810436935468840545356843 = 55429070625903692564428708224 := by
  rw [← show ((([(43, 1), (1658131897, 1), (795919661150545033, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_43, prime_fortyEightAT_1658131897, prime_fortyEightAT_795919661150545033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356844 : Nat.totient 56748810436935468840545356844 = 25794725895255583825400250000 := by
  rw [← show ((([(2, 2), (11, 1), (137251, 1), (9396985754191469517451, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_11, prime_fortyEightAT_137251, prime_fortyEightAT_9396985754191469517451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356845 : Nat.totient 56748810436935468840545356845 = 30266031540250119928900933728 := by
  rw [← show ((([(3, 2), (5, 1), (43687663, 1), (28865922088264225807, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_43687663, prime_fortyEightAT_28865922088264225807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356846 : Nat.totient 56748810436935468840545356846 = 27138810770769310564463043840 := by
  rw [← show ((([(2, 1), (23, 1), (14489, 1), (527381, 1), (161449252589470789, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_23, prime_fortyEightAT_14489, prime_fortyEightAT_527381, prime_fortyEightAT_161449252589470789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356847 : Nat.totient 56748810436935468840545356847 = 54917016350342052436106536960 := by
  rw [← show ((([(47, 1), (89, 1), (176021, 1), (1244387117, 1), (61936820537, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_47, prime_fortyEightAT_89, prime_fortyEightAT_176021, prime_fortyEightAT_1244387117, prime_fortyEightAT_61936820537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356848 : Nat.totient 56748810436935468840545356848 = 18728877245652730232015619072 := by
  rw [← show ((([(2, 4), (3, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_103, prime_fortyEightAT_5009, prime_fortyEightAT_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356849 : Nat.totient 56748810436935468840545356849 = 48338066542271336962545523200 := by
  rw [← show ((([(7, 2), (233, 1), (521, 1), (23627, 1), (403792693884455891, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_7, prime_fortyEightAT_233, prime_fortyEightAT_521, prime_fortyEightAT_23627, prime_fortyEightAT_403792693884455891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356850 : Nat.totient 56748810436935468840545356850 = 22699392272115887813462838720 := by
  rw [← show ((([(2, 1), (5, 2), (172093, 1), (6595132914986137593109, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_172093, prime_fortyEightAT_6595132914986137593109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356851 : Nat.totient 56748810436935468840545356851 = 35590929309116003197430931456 := by
  rw [← show ((([(3, 1), (17, 1), (2287, 1), (59513, 1), (930659839, 1), (8784511289, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_17, prime_fortyEightAT_2287, prime_fortyEightAT_59513, prime_fortyEightAT_930659839, prime_fortyEightAT_8784511289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356852 : Nat.totient 56748810436935468840545356852 = 26128733700766601504660981760 := by
  rw [← show ((([(2, 2), (13, 1), (431, 1), (11719, 1), (1228273, 1), (9574219, 1), (18373307, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_13, prime_fortyEightAT_431, prime_fortyEightAT_11719, prime_fortyEightAT_1228273, prime_fortyEightAT_9574219, prime_fortyEightAT_18373307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356853 : Nat.totient 56748810436935468840545356853 = 55678078164536250609368872144 := by
  rw [← show ((([(53, 1), (16652980983983, 1), (64296733024847, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_53, prime_fortyEightAT_16652980983983, prime_fortyEightAT_64296733024847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356854 : Nat.totient 56748810436935468840545356854 = 18795761964798830945561441664 := by
  rw [← show ((([(2, 1), (3, 3), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_227, prime_fortyEightAT_509, prime_fortyEightAT_106363, prime_fortyEightAT_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356855 : Nat.totient 56748810436935468840545356855 = 41271862135953068247669350400 := by
  rw [← show ((([(5, 1), (11, 1), (1031796553398826706191733761, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_11, prime_fortyEightAT_1031796553398826706191733761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356856 : Nat.totient 56748810436935468840545356856 = 24244040422500088944487092480 := by
  rw [← show ((([(2, 3), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_7, prime_fortyEightAT_331, prime_fortyEightAT_7129, prime_fortyEightAT_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356857 : Nat.totient 56748810436935468840545356857 = 35819133653654819952255300672 := by
  rw [← show ((([(3, 1), (19, 1), (1613, 1), (132501777739, 1), (4658282623343, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_19, prime_fortyEightAT_1613, prime_fortyEightAT_132501777739, prime_fortyEightAT_4658282623343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356858 : Nat.totient 56748810436935468840545356858 = 26994618520847220352880332800 := by
  rw [← show ((([(2, 1), (29, 2), (73, 1), (1069, 1), (34591, 1), (1856137, 1), (6733751111, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_29, prime_fortyEightAT_73, prime_fortyEightAT_1069, prime_fortyEightAT_34591, prime_fortyEightAT_1856137, prime_fortyEightAT_6733751111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356859 : Nat.totient 56748810436935468840545356859 = 55503556070809879501185153024 := by
  rw [← show ((([(59, 1), (197, 1), (243917, 1), (20016883181133315649, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_59, prime_fortyEightAT_197, prime_fortyEightAT_243917, prime_fortyEightAT_20016883181133315649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356860 : Nat.totient 56748810436935468840545356860 = 14976786759142478278239616000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_107, prime_fortyEightAT_1013, prime_fortyEightAT_144417341, prime_fortyEightAT_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356861 : Nat.totient 56748810436935468840545356861 = 55586190621259370793314764800 := by
  rw [← show ((([(61, 1), (241, 1), (80819, 1), (4787273, 1), (9977189429203, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_61, prime_fortyEightAT_241, prime_fortyEightAT_80819, prime_fortyEightAT_4787273, prime_fortyEightAT_9977189429203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356862 : Nat.totient 56748810436935468840545356862 = 27458251431864542401124476800 := by
  rw [← show ((([(2, 1), (31, 1), (53173, 1), (82763, 1), (12444181, 1), (16713652379, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_31, prime_fortyEightAT_53173, prime_fortyEightAT_82763, prime_fortyEightAT_12444181, prime_fortyEightAT_16713652379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356863 : Nat.totient 56748810436935468840545356863 = 31796826185607266836323532800 := by
  rw [← show ((([(3, 2), (7, 1), (71, 2), (353, 1), (389, 1), (17573, 1), (74050722409721, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_7, prime_fortyEightAT_71, prime_fortyEightAT_353, prime_fortyEightAT_389, prime_fortyEightAT_17573, prime_fortyEightAT_74050722409721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356864 : Nat.totient 56748810436935468840545356864 = 28320986566452283220282572800 := by
  rw [← show ((([(2, 6), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_769, prime_fortyEightAT_2143, prime_fortyEightAT_8597, prime_fortyEightAT_9792301, prime_fortyEightAT_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356865 : Nat.totient 56748810436935468840545356865 = 41766155628963014773207756800 := by
  rw [← show ((([(5, 1), (13, 3), (467, 1), (1423, 1), (2341, 1), (12323, 1), (153733, 1), (1752871, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_13, prime_fortyEightAT_467, prime_fortyEightAT_1423, prime_fortyEightAT_2341, prime_fortyEightAT_12323, prime_fortyEightAT_153733, prime_fortyEightAT_1752871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356866 : Nat.totient 56748810436935468840545356866 = 17196407574338606892000215040 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_11, prime_fortyEightAT_85313, prime_fortyEightAT_219959393, prime_fortyEightAT_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356867 : Nat.totient 56748810436935468840545356867 = 56739493116376300265318976840 := by
  rw [← show ((([(6091, 1), (115620599, 1), (80581054769871263, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_6091, prime_fortyEightAT_115620599, prime_fortyEightAT_80581054769871263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356868 : Nat.totient 56748810436935468840545356868 = 26661326887217153485174686720 := by
  rw [← show ((([(2, 2), (17, 1), (607, 1), (324023303, 1), (4243096546919081, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_17, prime_fortyEightAT_607, prime_fortyEightAT_324023303, prime_fortyEightAT_4243096546919081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356869 : Nat.totient 56748810436935468840545356869 = 36187647232007963992623496448 := by
  rw [← show ((([(3, 1), (23, 1), (11527331273, 1), (71347522561263737, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_23, prime_fortyEightAT_11527331273, prime_fortyEightAT_71347522561263737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356870 : Nat.totient 56748810436935468840545356870 = 19456735006938536767486204416 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1814437336489, 1), (446803687100569, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_7, prime_fortyEightAT_1814437336489, prime_fortyEightAT_446803687100569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356871 : Nat.totient 56748810436935468840545356871 = 56738169369911854464239230152 := by
  rw [← show ((([(5333, 1), (10641067023614376306121387, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5333, prime_fortyEightAT_10641067023614376306121387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356872 : Nat.totient 56748810436935468840545356872 = 18858596751130786945731072000 := by
  rw [← show ((([(2, 3), (3, 2), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_421, prime_fortyEightAT_1483, prime_fortyEightAT_2072201, prime_fortyEightAT_2567179, prime_fortyEightAT_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356873 : Nat.totient 56748810436935468840545356873 = 56748795276578153250994694608 := by
  rw [← show ((([(3743237, 1), (15160357315589546919029, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3743237, prime_fortyEightAT_15160357315589546919029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356874 : Nat.totient 56748810436935468840545356874 = 27600733235461146457463324928 := by
  rw [← show ((([(2, 1), (37, 1), (4079, 1), (992263, 1), (276413069, 1), (685466077, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_37, prime_fortyEightAT_4079, prime_fortyEightAT_992263, prime_fortyEightAT_276413069, prime_fortyEightAT_685466077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356875 : Nat.totient 56748810436935468840545356875 = 30265461571413106418648544000 := by
  rw [← show ((([(3, 1), (5, 4), (55897, 1), (1036459, 1), (522414067849459, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_55897, prime_fortyEightAT_1036459, prime_fortyEightAT_522414067849459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356876 : Nat.totient 56748810436935468840545356876 = 26480901336973829372953497600 := by
  rw [← show ((([(2, 2), (19, 2), (101, 1), (199, 1), (119737, 1), (21706837, 1), (752298509, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_19, prime_fortyEightAT_101, prime_fortyEightAT_199, prime_fortyEightAT_119737, prime_fortyEightAT_21706837, prime_fortyEightAT_752298509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356877 : Nat.totient 56748810436935468840545356877 = 44219852288521144551074304000 := by
  rw [← show ((([(7, 1), (11, 1), (736997538142019075851238401, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_7, prime_fortyEightAT_11, prime_fortyEightAT_736997538142019075851238401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356878 : Nat.totient 56748810436935468840545356878 = 17395640938693272227543377920 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_13, prime_fortyEightAT_307, prime_fortyEightAT_2011, prime_fortyEightAT_100888969, prime_fortyEightAT_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356879 : Nat.totient 56748810436935468840545356879 = 56301969409841564055316426680 := by
  rw [← show ((([(127, 1), (1804934610967, 1), (247566324202231, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_127, prime_fortyEightAT_1804934610967, prime_fortyEightAT_247566324202231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356880 : Nat.totient 56748810436935468840545356880 = 22588135713576510658820628480 := by
  rw [← show ((([(2, 4), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_281, prime_fortyEightAT_739, prime_fortyEightAT_3540386347, prime_fortyEightAT_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356881 : Nat.totient 56748810436935468840545356881 = 37832529846886276689377334432 := by
  rw [← show ((([(3, 4), (3972037, 1), (41136839, 1), (4287731098507, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_3972037, prime_fortyEightAT_41136839, prime_fortyEightAT_4287731098507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356882 : Nat.totient 56748810436935468840545356882 = 27269135460650116555872556800 := by
  rw [← show ((([(2, 1), (41, 1), (67, 1), (653273, 1), (15811511862622282211, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_41, prime_fortyEightAT_67, prime_fortyEightAT_653273, prime_fortyEightAT_15811511862622282211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356883 : Nat.totient 56748810436935468840545356883 = 56430939019698366256323590400 := by
  rw [← show ((([(313, 1), (419, 1), (57791, 1), (96821, 1), (77333671361899, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_313, prime_fortyEightAT_419, prime_fortyEightAT_57791, prime_fortyEightAT_96821, prime_fortyEightAT_77333671361899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356884 : Nat.totient 56748810436935468840545356884 = 16199029605601766108774387808 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_7, prime_fortyEightAT_1087, prime_fortyEightAT_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356885 : Nat.totient 56748810436935468840545356885 = 42726407189092929225026636800 := by
  rw [← show ((([(5, 1), (17, 1), (20261, 1), (32951634369673100648621, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_17, prime_fortyEightAT_20261, prime_fortyEightAT_32951634369673100648621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356886 : Nat.totient 56748810436935468840545356886 = 27703145558829412790105702400 := by
  rw [← show ((([(2, 1), (43, 1), (2441, 1), (1127537, 1), (2422033, 1), (98987344441, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_43, prime_fortyEightAT_2441, prime_fortyEightAT_1127537, prime_fortyEightAT_2422033, prime_fortyEightAT_98987344441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356887 : Nat.totient 56748810436935468840545356887 = 36527969936418232816902758400 := by
  rw [← show ((([(3, 1), (29, 1), (652285177436039871730406401, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_29, prime_fortyEightAT_652285177436039871730406401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356888 : Nat.totient 56748810436935468840545356888 = 25794518671190466351030764160 := by
  rw [← show ((([(2, 3), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_11, prime_fortyEightAT_97327, prime_fortyEightAT_208223, prime_fortyEightAT_4129087, prime_fortyEightAT_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356889 : Nat.totient 56748810436935468840545356889 = 56744937585223370466425030160 := by
  rw [← show ((([(14653, 1), (9702444491, 1), (399161867612743, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_14653, prime_fortyEightAT_9702444491, prime_fortyEightAT_399161867612743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356890 : Nat.totient 56748810436935468840545356890 = 15132788778754478100226643712 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_5, prime_fortyEightAT_66569, prime_fortyEightAT_1596046247, prime_fortyEightAT_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356891 : Nat.totient 56748810436935468840545356891 = 44900157661586192308435344288 := by
  rw [← show ((([(7, 1), (13, 1), (960259579, 1), (649421588852263219, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_7, prime_fortyEightAT_13, prime_fortyEightAT_960259579, prime_fortyEightAT_649421588852263219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356892 : Nat.totient 56748810436935468840545356892 = 27031458980913175241877946368 := by
  rw [← show ((([(2, 2), (23, 1), (449, 1), (557, 1), (128239, 1), (73816529, 1), (260551547, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_23, prime_fortyEightAT_449, prime_fortyEightAT_557, prime_fortyEightAT_128239, prime_fortyEightAT_73816529, prime_fortyEightAT_260551547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356893 : Nat.totient 56748810436935468840545356893 = 36562152685319838135580704000 := by
  rw [← show ((([(3, 1), (31, 1), (839, 1), (6197, 1), (82301, 1), (1426018778793047, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_31, prime_fortyEightAT_839, prime_fortyEightAT_6197, prime_fortyEightAT_82301, prime_fortyEightAT_1426018778793047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356894 : Nat.totient 56748810436935468840545356894 = 27770694469136337280435881984 := by
  rw [← show ((([(2, 1), (47, 1), (20563414774369, 1), (29358487194529, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_47, prime_fortyEightAT_20563414774369, prime_fortyEightAT_29358487194529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356895 : Nat.totient 56748810436935468840545356895 = 43009624751416294778495779104 := by
  rw [← show ((([(5, 1), (19, 1), (54620595583, 1), (10936458911884927, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_5, prime_fortyEightAT_19, prime_fortyEightAT_54620595583, prime_fortyEightAT_10936458911884927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356896 : Nat.totient 56748810436935468840545356896 = 18916270130173191852230595200 := by
  rw [← show ((([(2, 5), (3, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_3, prime_fortyEightAT_1222615931, prime_fortyEightAT_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356897 : Nat.totient 56748810436935468840545356897 = 56707753377922997501981337984 := by
  rw [← show ((([(1429, 1), (42169, 1), (941740464079439835397, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_1429, prime_fortyEightAT_42169, prime_fortyEightAT_941740464079439835397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356898 : Nat.totient 56748810436935468840545356898 = 24317574797338797167596763136 := by
  rw [← show ((([(2, 1), (7, 2), (8209, 1), (63793, 1), (971781007, 1), (1137886639, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_7, prime_fortyEightAT_8209, prime_fortyEightAT_63793, prime_fortyEightAT_971781007, prime_fortyEightAT_1137886639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356899 : Nat.totient 56748810436935468840545356899 = 34383389001736719769617672000 := by
  rw [← show ((([(3, 2), (11, 1), (3499, 1), (13053027349, 1), (12550654586551, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_3, prime_fortyEightAT_11, prime_fortyEightAT_3499, prime_fortyEightAT_13053027349, prime_fortyEightAT_12550654586551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyEightAT_56748810436935468840545356900 : Nat.totient 56748810436935468840545356900 = 22699175643026812723343603200 := by
  rw [← show ((([(2, 2), (5, 2), (65129, 1), (8713293684370321798361, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935468840545356900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyEightAT_2, prime_fortyEightAT_5, prime_fortyEightAT_65129, prime_fortyEightAT_8713293684370321798361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyEightAT : certifiedKill 1 56748810436935468840545356799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyEightAT_56748810436935468840545356800, phi_fortyEightAT_56748810436935468840545356801, phi_fortyEightAT_56748810436935468840545356802,
    phi_fortyEightAT_56748810436935468840545356803, phi_fortyEightAT_56748810436935468840545356804, phi_fortyEightAT_56748810436935468840545356805,
    phi_fortyEightAT_56748810436935468840545356806, phi_fortyEightAT_56748810436935468840545356807, phi_fortyEightAT_56748810436935468840545356808,
    phi_fortyEightAT_56748810436935468840545356809, phi_fortyEightAT_56748810436935468840545356810, phi_fortyEightAT_56748810436935468840545356811,
    phi_fortyEightAT_56748810436935468840545356812, phi_fortyEightAT_56748810436935468840545356813, phi_fortyEightAT_56748810436935468840545356814,
    phi_fortyEightAT_56748810436935468840545356815, phi_fortyEightAT_56748810436935468840545356816, phi_fortyEightAT_56748810436935468840545356817,
    phi_fortyEightAT_56748810436935468840545356818, phi_fortyEightAT_56748810436935468840545356819, phi_fortyEightAT_56748810436935468840545356820,
    phi_fortyEightAT_56748810436935468840545356821, phi_fortyEightAT_56748810436935468840545356822, phi_fortyEightAT_56748810436935468840545356823,
    phi_fortyEightAT_56748810436935468840545356824, phi_fortyEightAT_56748810436935468840545356825, phi_fortyEightAT_56748810436935468840545356826,
    phi_fortyEightAT_56748810436935468840545356827, phi_fortyEightAT_56748810436935468840545356828, phi_fortyEightAT_56748810436935468840545356829,
    phi_fortyEightAT_56748810436935468840545356830, phi_fortyEightAT_56748810436935468840545356831, phi_fortyEightAT_56748810436935468840545356832,
    phi_fortyEightAT_56748810436935468840545356833, phi_fortyEightAT_56748810436935468840545356834, phi_fortyEightAT_56748810436935468840545356835,
    phi_fortyEightAT_56748810436935468840545356836, phi_fortyEightAT_56748810436935468840545356837, phi_fortyEightAT_56748810436935468840545356838,
    phi_fortyEightAT_56748810436935468840545356839, phi_fortyEightAT_56748810436935468840545356840, phi_fortyEightAT_56748810436935468840545356841,
    phi_fortyEightAT_56748810436935468840545356842, phi_fortyEightAT_56748810436935468840545356843, phi_fortyEightAT_56748810436935468840545356844,
    phi_fortyEightAT_56748810436935468840545356845, phi_fortyEightAT_56748810436935468840545356846, phi_fortyEightAT_56748810436935468840545356847,
    phi_fortyEightAT_56748810436935468840545356848, phi_fortyEightAT_56748810436935468840545356849, phi_fortyEightAT_56748810436935468840545356850,
    phi_fortyEightAT_56748810436935468840545356851, phi_fortyEightAT_56748810436935468840545356852, phi_fortyEightAT_56748810436935468840545356853,
    phi_fortyEightAT_56748810436935468840545356854, phi_fortyEightAT_56748810436935468840545356855, phi_fortyEightAT_56748810436935468840545356856,
    phi_fortyEightAT_56748810436935468840545356857, phi_fortyEightAT_56748810436935468840545356858, phi_fortyEightAT_56748810436935468840545356859,
    phi_fortyEightAT_56748810436935468840545356860, phi_fortyEightAT_56748810436935468840545356861, phi_fortyEightAT_56748810436935468840545356862,
    phi_fortyEightAT_56748810436935468840545356863, phi_fortyEightAT_56748810436935468840545356864, phi_fortyEightAT_56748810436935468840545356865,
    phi_fortyEightAT_56748810436935468840545356866, phi_fortyEightAT_56748810436935468840545356867, phi_fortyEightAT_56748810436935468840545356868,
    phi_fortyEightAT_56748810436935468840545356869, phi_fortyEightAT_56748810436935468840545356870, phi_fortyEightAT_56748810436935468840545356871,
    phi_fortyEightAT_56748810436935468840545356872, phi_fortyEightAT_56748810436935468840545356873, phi_fortyEightAT_56748810436935468840545356874,
    phi_fortyEightAT_56748810436935468840545356875, phi_fortyEightAT_56748810436935468840545356876, phi_fortyEightAT_56748810436935468840545356877,
    phi_fortyEightAT_56748810436935468840545356878, phi_fortyEightAT_56748810436935468840545356879, phi_fortyEightAT_56748810436935468840545356880,
    phi_fortyEightAT_56748810436935468840545356881, phi_fortyEightAT_56748810436935468840545356882, phi_fortyEightAT_56748810436935468840545356883,
    phi_fortyEightAT_56748810436935468840545356884, phi_fortyEightAT_56748810436935468840545356885, phi_fortyEightAT_56748810436935468840545356886,
    phi_fortyEightAT_56748810436935468840545356887, phi_fortyEightAT_56748810436935468840545356888, phi_fortyEightAT_56748810436935468840545356889,
    phi_fortyEightAT_56748810436935468840545356890, phi_fortyEightAT_56748810436935468840545356891, phi_fortyEightAT_56748810436935468840545356892,
    phi_fortyEightAT_56748810436935468840545356893, phi_fortyEightAT_56748810436935468840545356894, phi_fortyEightAT_56748810436935468840545356895,
    phi_fortyEightAT_56748810436935468840545356896, phi_fortyEightAT_56748810436935468840545356897, phi_fortyEightAT_56748810436935468840545356898,
    phi_fortyEightAT_56748810436935468840545356899, phi_fortyEightAT_56748810436935468840545356900
  ]

end TotientTailPeriodKiller
end Erdos249257
