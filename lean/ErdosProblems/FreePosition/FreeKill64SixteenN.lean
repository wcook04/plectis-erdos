import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixteenNFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixteenNFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixteenNFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixteenNFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixteenNFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixteenNFastPow a n * sixteenNFastPow a n * a
        else sixteenNFastPow a n * sixteenNFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixteenN_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixteenN_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixteenN_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixteenN_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixteenN_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixteenN_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixteenN_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixteenN_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixteenN_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixteenN_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixteenN_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixteenN_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixteenN_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixteenN_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixteenN_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixteenN_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixteenN_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixteenN_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixteenN_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixteenN_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixteenN_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixteenN_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixteenN_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixteenN_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixteenN_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixteenN_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixteenN_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixteenN_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixteenN_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixteenN_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixteenN_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixteenN_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixteenN_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixteenN_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixteenN_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixteenN_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixteenN_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixteenN_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixteenN_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixteenN_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixteenN_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixteenN_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixteenN_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixteenN_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixteenN_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixteenN_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixteenN_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixteenN_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixteenN_233 : Nat.Prime 233 := by norm_num
private theorem prime_sixteenN_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixteenN_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixteenN_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixteenN_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixteenN_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixteenN_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixteenN_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixteenN_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixteenN_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixteenN_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixteenN_367 : Nat.Prime 367 := by norm_num
private theorem prime_sixteenN_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixteenN_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixteenN_383 : Nat.Prime 383 := by norm_num
private theorem prime_sixteenN_389 : Nat.Prime 389 := by norm_num
private theorem prime_sixteenN_397 : Nat.Prime 397 := by norm_num
private theorem prime_sixteenN_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixteenN_409 : Nat.Prime 409 := by norm_num
private theorem prime_sixteenN_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixteenN_421 : Nat.Prime 421 := by norm_num
private theorem prime_sixteenN_431 : Nat.Prime 431 := by norm_num
private theorem prime_sixteenN_439 : Nat.Prime 439 := by norm_num
private theorem prime_sixteenN_449 : Nat.Prime 449 := by norm_num
private theorem prime_sixteenN_463 : Nat.Prime 463 := by norm_num
private theorem prime_sixteenN_467 : Nat.Prime 467 := by norm_num
private theorem prime_sixteenN_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixteenN_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixteenN_499 : Nat.Prime 499 := by norm_num
private theorem prime_sixteenN_503 : Nat.Prime 503 := by norm_num
private theorem prime_sixteenN_509 : Nat.Prime 509 := by norm_num
private theorem prime_sixteenN_547 : Nat.Prime 547 := by norm_num
private theorem prime_sixteenN_563 : Nat.Prime 563 := by norm_num
private theorem prime_sixteenN_641 : Nat.Prime 641 := by norm_num
private theorem prime_sixteenN_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixteenN_653 : Nat.Prime 653 := by norm_num
private theorem prime_sixteenN_661 : Nat.Prime 661 := by norm_num
private theorem prime_sixteenN_677 : Nat.Prime 677 := by norm_num
private theorem prime_sixteenN_709 : Nat.Prime 709 := by norm_num
private theorem prime_sixteenN_719 : Nat.Prime 719 := by norm_num
private theorem prime_sixteenN_739 : Nat.Prime 739 := by norm_num
private theorem prime_sixteenN_743 : Nat.Prime 743 := by norm_num
private theorem prime_sixteenN_761 : Nat.Prime 761 := by norm_num
private theorem prime_sixteenN_773 : Nat.Prime 773 := by norm_num
private theorem prime_sixteenN_811 : Nat.Prime 811 := by norm_num
private theorem prime_sixteenN_821 : Nat.Prime 821 := by norm_num
private theorem prime_sixteenN_827 : Nat.Prime 827 := by norm_num
private theorem prime_sixteenN_839 : Nat.Prime 839 := by norm_num
private theorem prime_sixteenN_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixteenN_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixteenN_881 : Nat.Prime 881 := by norm_num
private theorem prime_sixteenN_887 : Nat.Prime 887 := by norm_num
private theorem prime_sixteenN_907 : Nat.Prime 907 := by norm_num
private theorem prime_sixteenN_911 : Nat.Prime 911 := by norm_num
private theorem prime_sixteenN_937 : Nat.Prime 937 := by norm_num
private theorem prime_sixteenN_941 : Nat.Prime 941 := by norm_num
private theorem prime_sixteenN_953 : Nat.Prime 953 := by norm_num
private theorem prime_sixteenN_967 : Nat.Prime 967 := by norm_num
private theorem prime_sixteenN_983 : Nat.Prime 983 := by norm_num
private theorem prime_sixteenN_991 : Nat.Prime 991 := by norm_num
private theorem prime_sixteenN_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_sixteenN_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_sixteenN_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_sixteenN_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_sixteenN_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_sixteenN_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_sixteenN_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_sixteenN_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_sixteenN_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_sixteenN_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_sixteenN_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_sixteenN_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_sixteenN_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_sixteenN_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_sixteenN_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_sixteenN_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_sixteenN_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_sixteenN_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_sixteenN_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_sixteenN_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_sixteenN_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_sixteenN_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_sixteenN_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_sixteenN_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_sixteenN_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_sixteenN_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_sixteenN_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_sixteenN_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_sixteenN_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_sixteenN_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_sixteenN_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_sixteenN_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_sixteenN_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_sixteenN_2789 : Nat.Prime 2789 := by norm_num
private theorem prime_sixteenN_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_sixteenN_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_sixteenN_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_sixteenN_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_sixteenN_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_sixteenN_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_sixteenN_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_sixteenN_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_sixteenN_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_sixteenN_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_sixteenN_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_sixteenN_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_sixteenN_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_sixteenN_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_sixteenN_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_sixteenN_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_sixteenN_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_sixteenN_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_sixteenN_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_sixteenN_4513 : Nat.Prime 4513 := by norm_num
private theorem prime_sixteenN_4549 : Nat.Prime 4549 := by norm_num
private theorem prime_sixteenN_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_sixteenN_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_sixteenN_5413 : Nat.Prime 5413 := by norm_num
private theorem prime_sixteenN_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_sixteenN_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_sixteenN_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_sixteenN_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_sixteenN_5987 : Nat.Prime 5987 := by norm_num
private theorem prime_sixteenN_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_sixteenN_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_sixteenN_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_sixteenN_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_sixteenN_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_sixteenN_6997 : Nat.Prime 6997 := by norm_num
private theorem prime_sixteenN_7229 : Nat.Prime 7229 := by norm_num
private theorem prime_sixteenN_7349 : Nat.Prime 7349 := by norm_num
private theorem prime_sixteenN_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_sixteenN_8101 : Nat.Prime 8101 := by norm_num
private theorem prime_sixteenN_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_sixteenN_8707 : Nat.Prime 8707 := by norm_num
private theorem prime_sixteenN_8747 : Nat.Prime 8747 := by norm_num
private theorem prime_sixteenN_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_sixteenN_9311 : Nat.Prime 9311 := by norm_num
private theorem prime_sixteenN_9419 : Nat.Prime 9419 := by norm_num
private theorem prime_sixteenN_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_sixteenN_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_sixteenN_10739 : Nat.Prime 10739 := by norm_num
private theorem prime_sixteenN_10883 : Nat.Prime 10883 := by norm_num
private theorem prime_sixteenN_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_sixteenN_11867 : Nat.Prime 11867 := by norm_num
private theorem prime_sixteenN_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_sixteenN_12251 : Nat.Prime 12251 := by norm_num
private theorem prime_sixteenN_13049 : Nat.Prime 13049 := by norm_num
private theorem prime_sixteenN_13099 : Nat.Prime 13099 := by norm_num
private theorem prime_sixteenN_13291 : Nat.Prime 13291 := by norm_num
private theorem prime_sixteenN_13309 : Nat.Prime 13309 := by norm_num
private theorem prime_sixteenN_13693 : Nat.Prime 13693 := by norm_num
private theorem prime_sixteenN_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_sixteenN_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_sixteenN_15131 : Nat.Prime 15131 := by norm_num
private theorem prime_sixteenN_15287 : Nat.Prime 15287 := by norm_num
private theorem prime_sixteenN_15667 : Nat.Prime 15667 := by norm_num
private theorem prime_sixteenN_15797 : Nat.Prime 15797 := by norm_num
private theorem prime_sixteenN_15907 : Nat.Prime 15907 := by norm_num
private theorem prime_sixteenN_17417 : Nat.Prime 17417 := by norm_num
private theorem prime_sixteenN_17491 : Nat.Prime 17491 := by norm_num
private theorem prime_sixteenN_17573 : Nat.Prime 17573 := by norm_num
private theorem prime_sixteenN_17737 : Nat.Prime 17737 := by norm_num
private theorem prime_sixteenN_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_sixteenN_18973 : Nat.Prime 18973 := by norm_num
private theorem prime_sixteenN_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_sixteenN_19073 : Nat.Prime 19073 := by norm_num
private theorem prime_sixteenN_19427 : Nat.Prime 19427 := by norm_num
private theorem prime_sixteenN_19763 : Nat.Prime 19763 := by norm_num
private theorem prime_sixteenN_20129 : Nat.Prime 20129 := by norm_num
private theorem prime_sixteenN_21517 : Nat.Prime 21517 := by norm_num
private theorem prime_sixteenN_21851 : Nat.Prime 21851 := by norm_num
private theorem prime_sixteenN_22397 : Nat.Prime 22397 := by norm_num
private theorem prime_sixteenN_22973 : Nat.Prime 22973 := by norm_num
private theorem prime_sixteenN_24971 : Nat.Prime 24971 := by norm_num
private theorem prime_sixteenN_25307 : Nat.Prime 25307 := by norm_num
private theorem prime_sixteenN_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_sixteenN_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_sixteenN_29021 : Nat.Prime 29021 := by norm_num
private theorem prime_sixteenN_30071 : Nat.Prime 30071 := by norm_num
private theorem prime_sixteenN_30557 : Nat.Prime 30557 := by norm_num
private theorem prime_sixteenN_31183 : Nat.Prime 31183 := by norm_num
private theorem prime_sixteenN_31723 : Nat.Prime 31723 := by norm_num
private theorem prime_sixteenN_32783 : Nat.Prime 32783 := by norm_num
private theorem prime_sixteenN_34301 : Nat.Prime 34301 := by norm_num
private theorem prime_sixteenN_34667 : Nat.Prime 34667 := by norm_num
private theorem prime_sixteenN_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_sixteenN_35461 : Nat.Prime 35461 := by norm_num
private theorem prime_sixteenN_36341 : Nat.Prime 36341 := by norm_num
private theorem prime_sixteenN_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_sixteenN_41669 : Nat.Prime 41669 := by norm_num
private theorem prime_sixteenN_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_sixteenN_45893 : Nat.Prime 45893 := by norm_num
private theorem prime_sixteenN_49627 : Nat.Prime 49627 := by norm_num
private theorem prime_sixteenN_50833 : Nat.Prime 50833 := by norm_num
private theorem prime_sixteenN_53017 : Nat.Prime 53017 := by norm_num
private theorem prime_sixteenN_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_sixteenN_54287 : Nat.Prime 54287 := by norm_num
private theorem prime_sixteenN_55843 : Nat.Prime 55843 := by norm_num
private theorem prime_sixteenN_55897 : Nat.Prime 55897 := by norm_num
private theorem prime_sixteenN_58337 : Nat.Prime 58337 := by norm_num
private theorem prime_sixteenN_59513 : Nat.Prime 59513 := by norm_num
private theorem prime_sixteenN_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_sixteenN_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_sixteenN_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_sixteenN_62477 : Nat.Prime 62477 := by norm_num
private theorem prime_sixteenN_64091 : Nat.Prime 64091 := by norm_num
private theorem prime_sixteenN_64333 : Nat.Prime 64333 := by norm_num
private theorem prime_sixteenN_64439 : Nat.Prime 64439 := by norm_num
private theorem prime_sixteenN_65927 : Nat.Prime 65927 := by norm_num
private theorem prime_sixteenN_66553 : Nat.Prime 66553 := by norm_num
private theorem prime_sixteenN_66569 : Nat.Prime 66569 := by norm_num
private theorem prime_sixteenN_68891 : Nat.Prime 68891 := by norm_num
private theorem prime_sixteenN_71171 : Nat.Prime 71171 := by norm_num
private theorem prime_sixteenN_73771 : Nat.Prime 73771 := by norm_num
private theorem prime_sixteenN_80191 : Nat.Prime 80191 := by norm_num
private theorem prime_sixteenN_81283 : Nat.Prime 81283 := by norm_num
private theorem prime_sixteenN_82301 : Nat.Prime 82301 := by norm_num
private theorem prime_sixteenN_85243 : Nat.Prime 85243 := by norm_num
private theorem prime_sixteenN_85313 : Nat.Prime 85313 := by norm_num
private theorem prime_sixteenN_85829 : Nat.Prime 85829 := by norm_num
private theorem prime_sixteenN_90031 : Nat.Prime 90031 := by norm_num
private theorem prime_sixteenN_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_sixteenN_101107 : Nat.Prime 101107 := by norm_num
private theorem prime_sixteenN_102593 : Nat.Prime 102593 := by norm_num
private theorem prime_sixteenN_103393 : Nat.Prime 103393 := by norm_num
private theorem prime_sixteenN_106363 : Nat.Prime 106363 := by norm_num
private theorem prime_sixteenN_108271 : Nat.Prime 108271 := by norm_num
private theorem prime_sixteenN_115883 : Nat.Prime 115883 := by norm_num
private theorem prime_sixteenN_117053 : Nat.Prime 117053 := by norm_num
private theorem prime_sixteenN_120049 : Nat.Prime 120049 := by norm_num
private theorem prime_sixteenN_148721 : Nat.Prime 148721 := by norm_num
private theorem prime_sixteenN_155413 : Nat.Prime 155413 := by norm_num
private theorem prime_sixteenN_157747 : Nat.Prime 157747 := by norm_num
private theorem prime_sixteenN_158077 : Nat.Prime 158077 := by norm_num
private theorem prime_sixteenN_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_sixteenN_177409 : Nat.Prime 177409 := by norm_num
private theorem prime_sixteenN_180497 : Nat.Prime 180497 := by norm_num
private theorem prime_sixteenN_181219 : Nat.Prime 181219 := by norm_num
private theorem prime_sixteenN_185177 : Nat.Prime 185177 := by norm_num
private theorem prime_sixteenN_193451 : Nat.Prime 193451 := by norm_num
private theorem prime_sixteenN_198977 : Nat.Prime 198977 := by norm_num
private theorem prime_sixteenN_204361 : Nat.Prime 204361 := by norm_num
private theorem prime_sixteenN_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_sixteenN_206813 : Nat.Prime 206813 := by norm_num
private theorem prime_sixteenN_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_sixteenN_212573 : Nat.Prime 212573 := by norm_num
private theorem prime_sixteenN_221461 : Nat.Prime 221461 := by norm_num
private theorem prime_sixteenN_229519 : Nat.Prime 229519 := by norm_num
private theorem prime_sixteenN_230539 : Nat.Prime 230539 := by norm_num
private theorem prime_sixteenN_231169 : Nat.Prime 231169 := by norm_num
private theorem prime_sixteenN_239963 : Nat.Prime 239963 := by norm_num
private theorem prime_sixteenN_259907 : Nat.Prime 259907 := by norm_num
private theorem prime_sixteenN_293081 : Nat.Prime 293081 := by norm_num
private theorem prime_sixteenN_299287 : Nat.Prime 299287 := by norm_num
private theorem prime_sixteenN_307381 : Nat.Prime 307381 := by norm_num
private theorem prime_sixteenN_381761 : Nat.Prime 381761 := by norm_num
private theorem prime_sixteenN_382709 : Nat.Prime 382709 := by norm_num
private theorem prime_sixteenN_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_sixteenN_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_sixteenN_392299 : Nat.Prime 392299 := by norm_num
private theorem prime_sixteenN_402137 : Nat.Prime 402137 := by norm_num
private theorem prime_sixteenN_472559 : Nat.Prime 472559 := by norm_num
private theorem prime_sixteenN_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_sixteenN_562703 : Nat.Prime 562703 := by norm_num
private theorem prime_sixteenN_576617 : Nat.Prime 576617 := by norm_num
private theorem prime_sixteenN_595201 : Nat.Prime 595201 := by norm_num
private theorem prime_sixteenN_622967 : Nat.Prime 622967 := by norm_num
private theorem prime_sixteenN_638327 : Nat.Prime 638327 := by norm_num
private theorem prime_sixteenN_644549 : Nat.Prime 644549 := by norm_num
private theorem prime_sixteenN_656023 : Nat.Prime 656023 := by norm_num
private theorem prime_sixteenN_674701 : Nat.Prime 674701 := by norm_num
private theorem prime_sixteenN_713917 : Nat.Prime 713917 := by norm_num
private theorem prime_sixteenN_761203 : Nat.Prime 761203 := by norm_num
private theorem prime_sixteenN_772703 : Nat.Prime 772703 := by norm_num
private theorem prime_sixteenN_813613 : Nat.Prime 813613 := by norm_num
private theorem prime_sixteenN_834859 : Nat.Prime 834859 := by norm_num
private theorem prime_sixteenN_854771 : Nat.Prime 854771 := by norm_num
private theorem prime_sixteenN_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_sixteenN_1036459 : Nat.Prime 1036459 := by norm_num
private theorem prime_sixteenN_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_sixteenN_1257209 : Nat.Prime 1257209 := by norm_num
private theorem prime_sixteenN_1265779 : Nat.Prime 1265779 := by norm_num
private theorem prime_sixteenN_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_sixteenN_1427389 : Nat.Prime 1427389 := by norm_num
private theorem prime_sixteenN_1494473 : Nat.Prime 1494473 := by norm_num
private theorem prime_sixteenN_1578281 : Nat.Prime 1578281 := by norm_num
private theorem prime_sixteenN_1703843 : Nat.Prime 1703843 := by norm_num
private theorem prime_sixteenN_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_sixteenN_1916773 : Nat.Prime 1916773 := by norm_num
private theorem prime_sixteenN_1973467 : Nat.Prime 1973467 := by norm_num
private theorem prime_sixteenN_2022619 : Nat.Prime 2022619 := by norm_num
private theorem prime_sixteenN_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_sixteenN_2126213 : Nat.Prime 2126213 := by norm_num
private theorem prime_sixteenN_2351599 : Nat.Prime 2351599 := by norm_num
private theorem prime_sixteenN_2379253 : Nat.Prime 2379253 := by norm_num
private theorem prime_sixteenN_2509337 : Nat.Prime 2509337 := by norm_num
private theorem prime_sixteenN_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_sixteenN_2685877 : Nat.Prime 2685877 := by norm_num
private theorem prime_sixteenN_2732549 : Nat.Prime 2732549 := by norm_num
private theorem prime_sixteenN_2751247 : Nat.Prime 2751247 := by norm_num
private theorem prime_sixteenN_3477841 : Nat.Prime 3477841 := by norm_num
private theorem prime_sixteenN_3880249 : Nat.Prime 3880249 := by norm_num
private theorem prime_sixteenN_3972037 : Nat.Prime 3972037 := by norm_num
private theorem prime_sixteenN_3974227 : Nat.Prime 3974227 := by norm_num
private theorem prime_sixteenN_4203707 : Nat.Prime 4203707 := by norm_num
private theorem prime_sixteenN_4315799 : Nat.Prime 4315799 := by norm_num
private theorem prime_sixteenN_4384091 : Nat.Prime 4384091 := by norm_num
private theorem prime_sixteenN_4451401 : Nat.Prime 4451401 := by norm_num
private theorem prime_sixteenN_4924417 : Nat.Prime 4924417 := by norm_num
private theorem prime_sixteenN_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_sixteenN_5530901 : Nat.Prime 5530901 := by norm_num
private theorem prime_sixteenN_5729557 : Nat.Prime 5729557 := by norm_num
private theorem prime_sixteenN_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_sixteenN_6514591 : Nat.Prime 6514591 := by norm_num
private theorem prime_sixteenN_6643181 : Nat.Prime 6643181 := by norm_num
private theorem prime_sixteenN_6850243 : Nat.Prime 6850243 := by norm_num
private theorem prime_sixteenN_7010693 : Nat.Prime 7010693 := by norm_num
private theorem prime_sixteenN_7041049 : Nat.Prime 7041049 := by norm_num
private theorem prime_sixteenN_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_sixteenN_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_sixteenN_7281277 : Nat.Prime 7281277 := by norm_num
private theorem prime_sixteenN_7487737 : Nat.Prime 7487737 := by norm_num
private theorem prime_sixteenN_7682093 : Nat.Prime 7682093 := by norm_num
private theorem prime_sixteenN_8265919 : Nat.Prime 8265919 := by norm_num
private theorem prime_sixteenN_8592127 : Nat.Prime 8592127 := by norm_num
private theorem prime_sixteenN_9042907 : Nat.Prime 9042907 := by norm_num
private theorem prime_sixteenN_9124861 : Nat.Prime 9124861 := by norm_num
private theorem prime_sixteenN_9350807 : Nat.Prime 9350807 := by norm_num
private theorem prime_sixteenN_9420721 : Nat.Prime 9420721 := by norm_num
private theorem prime_sixteenN_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_sixteenN_10600781 : Nat.Prime 10600781 := by norm_num
private theorem prime_sixteenN_11239603 : Nat.Prime 11239603 := by norm_num
private theorem prime_sixteenN_11566843 : Nat.Prime 11566843 := by norm_num
private theorem prime_sixteenN_11731007 : Nat.Prime 11731007 := by norm_num
private theorem prime_sixteenN_13169249 : Nat.Prime 13169249 := by norm_num
private theorem prime_sixteenN_13509889 : Nat.Prime 13509889 := by norm_num
private theorem prime_sixteenN_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_sixteenN_15857351 : Nat.Prime 15857351 := by norm_num
private theorem prime_sixteenN_16205789 : Nat.Prime 16205789 := by norm_num
private theorem prime_sixteenN_17478479 : Nat.Prime 17478479 := by norm_num
private theorem prime_sixteenN_18321287 : Nat.Prime 18321287 := by norm_num
private theorem prime_sixteenN_18480383 : Nat.Prime 18480383 := by norm_num
private theorem prime_sixteenN_20082371 : Nat.Prime 20082371 := by norm_num
private theorem prime_sixteenN_20234143 : Nat.Prime 20234143 := by norm_num
private theorem prime_sixteenN_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_sixteenN_22421449 : Nat.Prime 22421449 := by norm_num
private theorem prime_sixteenN_23255671 : Nat.Prime 23255671 := by norm_num
private theorem prime_sixteenN_24581699 : Nat.Prime 24581699 := by norm_num
private theorem prime_sixteenN_25331881 : Nat.Prime 25331881 := by norm_num
private theorem prime_sixteenN_25593889 : Nat.Prime 25593889 := by norm_num
private theorem prime_sixteenN_25817069 : Nat.Prime 25817069 := by norm_num
private theorem prime_sixteenN_27506953 : Nat.Prime 27506953 := by norm_num
private theorem prime_sixteenN_27902741 : Nat.Prime 27902741 := by norm_num

private theorem prime_sixteenN_31896439 : Nat.Prime 31896439 := by
  apply lucas_primality 31896439 (7 : ZMod 31896439)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (653, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (653, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 31896439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_653
      · exact prime_sixteenN_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31896439) ^ 15948219 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31896439) ^ 10632146 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31896439) ^ 4556634 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31896439) ^ 48846 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31896439) ^ 27426 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_31916351 : Nat.Prime 31916351 := by
  apply lucas_primality 31916351 (11 : ZMod 31916351)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (638327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (638327, 1)] : List FactorBlock).map factorBlockValue).prod) = 31916351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_638327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 31916351) ^ 15958175 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 31916351) ^ 6383270 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 31916351) ^ 50 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_983
      · exact prime_sixteenN_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_36407143 : Nat.Prime 36407143 := by
  apply lucas_primality 36407143 (6 : ZMod 36407143)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2022619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2022619, 1)] : List FactorBlock).map factorBlockValue).prod) = 36407143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2022619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 36407143) ^ 18203571 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 36407143) ^ 12135714 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 36407143) ^ 18 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_39926713 : Nat.Prime 39926713 := by
  apply lucas_primality 39926713 (11 : ZMod 39926713)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 39926713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_23
      · exact prime_sixteenN_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39926713) ^ 19963356 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 13308904 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 5703816 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 1735944 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 3864 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_41136839 : Nat.Prime 41136839 := by
  apply lucas_primality 41136839 (7 : ZMod 41136839)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) = 41136839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_71171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 41136839) ^ 20568419 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 2419814 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 578 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_41734093 : Nat.Prime 41734093 := by
  apply lucas_primality 41734093 (2 : ZMod 41734093)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod) = 41734093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41734093) ^ 20867046 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 13911364 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 12 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_42001217 : Nat.Prime 42001217 := by
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_37
      · exact prime_sixteenN_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42001217) ^ 21000608 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 1135168 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 2368 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_42355637 : Nat.Prime 42355637 := by
  apply lucas_primality 42355637 (2 : ZMod 42355637)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod) = 42355637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_32783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42355637) ^ 21177818 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42355637) ^ 2491508 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42355637) ^ 2229244 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42355637) ^ 1292 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_43687663 : Nat.Prime 43687663 := by
  apply lucas_primality 43687663 (3 : ZMod 43687663)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) = 43687663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7281277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43687663) ^ 21843831 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 14562554 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 6 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_51634139 : Nat.Prime 51634139 := by
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51634139) ^ 25817069 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 51634139) ^ 2 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_60672923 : Nat.Prime 60672923 := by
  apply lucas_primality 60672923 (2 : ZMod 60672923)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (101, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (101, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) = 60672923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_67
      · exact prime_sixteenN_101
      · exact prime_sixteenN_4483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60672923) ^ 30336461 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 905566 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 600722 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 13534 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_70150373 : Nat.Prime 70150373 := by
  apply lucas_primality 70150373 (2 : ZMod 70150373)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 70150373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_37
      · exact prime_sixteenN_43
      · exact prime_sixteenN_73
      · exact prime_sixteenN_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70150373) ^ 35075186 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1895956 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1631404 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 960964 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 464572 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_1901
      · exact prime_sixteenN_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_75581171 : Nat.Prime 75581171 := by
  apply lucas_primality 75581171 (2 : ZMod 75581171)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) = 75581171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_47
      · exact prime_sixteenN_22973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75581171) ^ 37790585 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 15116234 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 10797310 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 1608110 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 3290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_77954273 : Nat.Prime 77954273 := by
  apply lucas_primality 77954273 (3 : ZMod 77954273)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod) = 77954273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_221461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 77954273) ^ 38977136 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 77954273) ^ 7086752 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 77954273) ^ 352 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_97678393 : Nat.Prime 97678393 := by
  apply lucas_primality 97678393 (11 : ZMod 97678393)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 97678393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_19
      · exact prime_sixteenN_71
      · exact prime_sixteenN_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 97678393) ^ 48839196 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 32559464 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 13954056 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 5140968 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 1375752 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 226632 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_100888969 : Nat.Prime 100888969 := by
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100888969) ^ 50444484 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 33629656 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 24 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_112228771 : Nat.Prime 112228771 := by
  apply lucas_primality 112228771 (2 : ZMod 112228771)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (101107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (101107, 1)] : List FactorBlock).map factorBlockValue).prod) = 112228771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_37
      · exact prime_sixteenN_101107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112228771) ^ 56114385 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112228771) ^ 37409590 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112228771) ^ 22445754 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112228771) ^ 3033210 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112228771) ^ 1110 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_13
      · exact prime_sixteenN_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_118970149 : Nat.Prime 118970149 := by
  apply lucas_primality 118970149 (2 : ZMod 118970149)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (53017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (53017, 1)] : List FactorBlock).map factorBlockValue).prod) = 118970149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_17
      · exact prime_sixteenN_53017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 118970149) ^ 59485074 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118970149) ^ 39656716 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118970149) ^ 10815468 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118970149) ^ 6998244 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118970149) ^ 2244 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_17
      · exact prime_sixteenN_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_137474033 : Nat.Prime 137474033 := by
  apply lucas_primality 137474033 (3 : ZMod 137474033)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (8592127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (8592127, 1)] : List FactorBlock).map factorBlockValue).prod) = 137474033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_8592127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 137474033) ^ 68737016 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 137474033) ^ 16 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_143826233 : Nat.Prime 143826233 := by
  apply lucas_primality 143826233 (3 : ZMod 143826233)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 143826233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_563
      · exact prime_sixteenN_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 143826233) ^ 71913116 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 13075112 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 255464 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 49544 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_144038591 : Nat.Prime 144038591 := by
  apply lucas_primality 144038591 (7 : ZMod 144038591)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 144038591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_827
      · exact prime_sixteenN_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144038591) ^ 72019295 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 28807718 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 174170 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 8270 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_144778493 : Nat.Prime 144778493 := by
  apply lucas_primality 144778493 (2 : ZMod 144778493)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (230539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (230539, 1)] : List FactorBlock).map factorBlockValue).prod) = 144778493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_157
      · exact prime_sixteenN_230539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144778493) ^ 72389246 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144778493) ^ 922156 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144778493) ^ 628 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_158385407 : Nat.Prime 158385407 := by
  apply lucas_primality 158385407 (5 : ZMod 158385407)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23, 1), (181219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23, 1), (181219, 1)] : List FactorBlock).map factorBlockValue).prod) = 158385407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_181219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 158385407) ^ 79192703 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 158385407) ^ 8336074 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 158385407) ^ 6886322 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 158385407) ^ 874 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_171113017 : Nat.Prime 171113017 := by
  apply lucas_primality 171113017 (5 : ZMod 171113017)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (367, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (367, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod) = 171113017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_367
      · exact prime_sixteenN_19427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 171113017) ^ 85556508 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 171113017) ^ 57037672 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 171113017) ^ 466248 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 171113017) ^ 8808 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_207033377 : Nat.Prime 207033377 := by
  apply lucas_primality 207033377 (3 : ZMod 207033377)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (31, 1), (18973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (31, 1), (18973, 1)] : List FactorBlock).map factorBlockValue).prod) = 207033377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_31
      · exact prime_sixteenN_18973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 207033377) ^ 103516688 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 207033377) ^ 18821216 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 207033377) ^ 6678496 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 207033377) ^ 10912 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_219959393 : Nat.Prime 219959393 := by
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_67
      · exact prime_sixteenN_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219959393) ^ 109979696 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 3282976 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 2144 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_224359867 : Nat.Prime 224359867 := by
  apply lucas_primality 224359867 (2 : ZMod 224359867)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod) = 224359867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_19
      · exact prime_sixteenN_656023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224359867) ^ 112179933 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 74786622 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 11808414 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 342 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_232001521 : Nat.Prime 232001521 := by
  apply lucas_primality 232001521 (7 : ZMod 232001521)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (31, 1), (31183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (31, 1), (31183, 1)] : List FactorBlock).map factorBlockValue).prod) = 232001521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_31
      · exact prime_sixteenN_31183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 232001521) ^ 116000760 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 77333840 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 46400304 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 7483920 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 7440 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_191
      · exact prime_sixteenN_383
      · exact prime_sixteenN_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_244140209 : Nat.Prime 244140209 := by
  apply lucas_primality 244140209 (3 : ZMod 244140209)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod) = 244140209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_13
      · exact prime_sixteenN_37
      · exact prime_sixteenN_31723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 244140209) ^ 122070104 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 18780016 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 6598384 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 7696 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_266476337 : Nat.Prime 266476337 := by
  apply lucas_primality 266476337 (3 : ZMod 266476337)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) = 266476337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_2379253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266476337) ^ 133238168 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 38068048 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 112 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_274948067 : Nat.Prime 274948067 := by
  apply lucas_primality 274948067 (2 : ZMod 274948067)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137474033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137474033, 1)] : List FactorBlock).map factorBlockValue).prod) = 274948067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_137474033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 274948067) ^ 137474033 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 274948067) ^ 2 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_67
      · exact prime_sixteenN_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_289267687 : Nat.Prime 289267687 := by
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 289267687) ^ 144633843 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 96422562 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 486 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_308134529 : Nat.Prime 308134529 := by
  apply lucas_primality 308134529 (3 : ZMod 308134529)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (185177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (185177, 1)] : List FactorBlock).map factorBlockValue).prod) = 308134529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_13
      · exact prime_sixteenN_185177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 308134529) ^ 154067264 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 308134529) ^ 23702656 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 308134529) ^ 1664 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_323746289 : Nat.Prime 323746289 := by
  apply lucas_primality 323746289 (3 : ZMod 323746289)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20234143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20234143, 1)] : List FactorBlock).map factorBlockValue).prod) = 323746289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_20234143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 323746289) ^ 161873144 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 323746289) ^ 16 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_361266151 : Nat.Prime 361266151 := by
  apply lucas_primality 361266151 (14 : ZMod 361266151)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (37, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (37, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 361266151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_17
      · exact prime_sixteenN_37
      · exact prime_sixteenN_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 361266151) ^ 180633075 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 120422050 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 72253230 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 51609450 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 21250950 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 9763950 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 361266151) ^ 660450 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_362808133 : Nat.Prime 362808133 := by
  apply lucas_primality 362808133 (5 : ZMod 362808133)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) = 362808133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_79
      · exact prime_sixteenN_382709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 362808133) ^ 181404066 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 120936044 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 4592508 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 948 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_364037539 : Nat.Prime 364037539 := by
  apply lucas_primality 364037539 (2 : ZMod 364037539)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (60672923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (60672923, 1)] : List FactorBlock).map factorBlockValue).prod) = 364037539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_60672923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 364037539) ^ 182018769 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 364037539) ^ 121345846 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 364037539) ^ 6 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_415741019 : Nat.Prime 415741019 := by
  apply lucas_primality 415741019 (2 : ZMod 415741019)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (379, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (379, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 415741019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_17
      · exact prime_sixteenN_379
      · exact prime_sixteenN_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 415741019) ^ 207870509 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 59391574 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 37794638 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 24455354 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 1096942 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 992222 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_440587493 : Nat.Prime 440587493 := by
  apply lucas_primality 440587493 (2 : ZMod 440587493)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (941, 1), (117053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (941, 1), (117053, 1)] : List FactorBlock).map factorBlockValue).prod) = 440587493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_941
      · exact prime_sixteenN_117053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 440587493) ^ 220293746 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 440587493) ^ 468212 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 440587493) ^ 3764 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_458961409 : Nat.Prime 458961409 := by
  apply lucas_primality 458961409 (19 : ZMod 458961409)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (103, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (103, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 458961409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_103
      · exact prime_sixteenN_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 458961409) ^ 229480704 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 458961409) ^ 152987136 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 458961409) ^ 4455936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 458961409) ^ 474624 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_516923423 : Nat.Prime 516923423 := by
  apply lucas_primality 516923423 (5 : ZMod 516923423)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (2509337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (2509337, 1)] : List FactorBlock).map factorBlockValue).prod) = 516923423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_103
      · exact prime_sixteenN_2509337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 516923423) ^ 258461711 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 516923423) ^ 5018674 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 516923423) ^ 206 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_561048421 : Nat.Prime 561048421 := by
  apply lucas_primality 561048421 (2 : ZMod 561048421)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (9350807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (9350807, 1)] : List FactorBlock).map factorBlockValue).prod) = 561048421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_9350807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 561048421) ^ 280524210 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 561048421) ^ 187016140 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 561048421) ^ 112209684 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 561048421) ^ 60 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_642191821 : Nat.Prime 642191821 := by
  apply lucas_primality 642191821 (2 : ZMod 642191821)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) = 642191821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_167
      · exact prime_sixteenN_64091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642191821) ^ 321095910 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 214063940 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 128438364 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 3845460 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 10020 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_685403783 : Nat.Prime 685403783 := by
  apply lucas_primality 685403783 (5 : ZMod 685403783)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (761, 1), (64333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (761, 1), (64333, 1)] : List FactorBlock).map factorBlockValue).prod) = 685403783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_761
      · exact prime_sixteenN_64333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 685403783) ^ 342701891 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 685403783) ^ 97914826 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 685403783) ^ 900662 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 685403783) ^ 10654 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_930659839 : Nat.Prime 930659839 := by
  apply lucas_primality 930659839 (3 : ZMod 930659839)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) = 930659839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_269
      · exact prime_sixteenN_576617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 930659839) ^ 465329919 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 310219946 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 3459702 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 1614 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_935451277 : Nat.Prime 935451277 := by
  apply lucas_primality 935451277 (5 : ZMod 935451277)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod) = 935451277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_77954273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 935451277) ^ 467725638 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 935451277) ^ 311817092 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 935451277) ^ 12 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1022142959 : Nat.Prime 1022142959 := by
  apply lucas_primality 1022142959 (13 : ZMod 1022142959)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (419, 1), (9311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (419, 1), (9311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022142959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_131
      · exact prime_sixteenN_419
      · exact prime_sixteenN_9311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1022142959) ^ 511071479 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1022142959) ^ 7802618 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1022142959) ^ 2439482 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1022142959) ^ 109778 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1088621057 : Nat.Prime 1088621057 := by
  apply lucas_primality 1088621057 (3 : ZMod 1088621057)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088621057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_2126213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1088621057) ^ 544310528 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1088621057) ^ 512 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1092560611 : Nat.Prime 1092560611 := by
  apply lucas_primality 1092560611 (10 : ZMod 1092560611)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (1916773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (1916773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1092560611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_19
      · exact prime_sixteenN_1916773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1092560611) ^ 546280305 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1092560611) ^ 364186870 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1092560611) ^ 218512122 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1092560611) ^ 57503190 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1092560611) ^ 570 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1115207957 : Nat.Prime 1115207957 := by
  apply lucas_primality 1115207957 (2 : ZMod 1115207957)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1031, 1), (15907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1031, 1), (15907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115207957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_1031
      · exact prime_sixteenN_15907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1115207957) ^ 557603978 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115207957) ^ 65600468 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115207957) ^ 1081676 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115207957) ^ 70108 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_29
      · exact prime_sixteenN_113
      · exact prime_sixteenN_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1239756391 : Nat.Prime 1239756391 := by
  apply lucas_primality 1239756391 (6 : ZMod 1239756391)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (259907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (259907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239756391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_53
      · exact prime_sixteenN_259907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1239756391) ^ 619878195 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1239756391) ^ 413252130 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1239756391) ^ 247951278 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1239756391) ^ 23391630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1239756391) ^ 4770 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_31
      · exact prime_sixteenN_59
      · exact prime_sixteenN_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1295475289 : Nat.Prime 1295475289 := by
  apply lucas_primality 1295475289 (7 : ZMod 1295475289)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (83, 1), (101, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (83, 1), (101, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295475289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_47
      · exact prime_sixteenN_83
      · exact prime_sixteenN_101
      · exact prime_sixteenN_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1295475289) ^ 647737644 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295475289) ^ 431825096 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295475289) ^ 27563304 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295475289) ^ 15608136 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295475289) ^ 12826488 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295475289) ^ 9456024 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1409138009 : Nat.Prime 1409138009 := by
  apply lucas_primality 1409138009 (3 : ZMod 1409138009)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (449, 1), (392299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (449, 1), (392299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409138009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_449
      · exact prime_sixteenN_392299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1409138009) ^ 704569004 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409138009) ^ 3138392 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409138009) ^ 3592 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_61
      · exact prime_sixteenN_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1440916409 : Nat.Prime 1440916409 := by
  apply lucas_primality 1440916409 (3 : ZMod 1440916409)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440916409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_59
      · exact prime_sixteenN_89
      · exact prime_sixteenN_34301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1440916409) ^ 720458204 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 24422312 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 16190072 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 42008 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1458322139 : Nat.Prime 1458322139 := by
  apply lucas_primality 1458322139 (2 : ZMod 1458322139)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (89, 1), (90031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (89, 1), (90031, 1)] : List FactorBlock).map factorBlockValue).prod) = 1458322139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_89
      · exact prime_sixteenN_90031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1458322139) ^ 729161069 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 208331734 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 112178626 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 16385642 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 16198 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1596046247 : Nat.Prime 1596046247 := by
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_19
      · exact prime_sixteenN_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1596046247) ^ 798023123 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 84002434 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 38 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1656564227 : Nat.Prime 1656564227 := by
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_101
      · exact prime_sixteenN_2521
      · exact prime_sixteenN_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1656564227) ^ 828282113 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 16401626 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 657106 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 509242 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2020679827 : Nat.Prime 2020679827 := by
  apply lucas_primality 2020679827 (2 : ZMod 2020679827)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (197, 1), (155413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (197, 1), (155413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020679827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_197
      · exact prime_sixteenN_155413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2020679827) ^ 1010339913 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020679827) ^ 673559942 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020679827) ^ 183698166 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020679827) ^ 10257258 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2020679827) ^ 13002 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2129669261 : Nat.Prime 2129669261 := by
  apply lucas_primality 2129669261 (2 : ZMod 2129669261)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2129669261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_887
      · exact prime_sixteenN_120049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2129669261) ^ 1064834630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 425933852 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 2400980 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 17740 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2143898431 : Nat.Prime 2143898431 := by
  apply lucas_primality 2143898431 (3 : ZMod 2143898431)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (562703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (562703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143898431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_127
      · exact prime_sixteenN_562703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2143898431) ^ 1071949215 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2143898431) ^ 714632810 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2143898431) ^ 428779686 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2143898431) ^ 16881090 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2143898431) ^ 3810 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2467612603 : Nat.Prime 2467612603 := by
  apply lucas_primality 2467612603 (2 : ZMod 2467612603)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 2), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 2), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2467612603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_115883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2467612603) ^ 1233806301 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467612603) ^ 822537534 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467612603) ^ 352516086 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467612603) ^ 189816354 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2467612603) ^ 21294 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2546581993 : Nat.Prime 2546581993 := by
  apply lucas_primality 2546581993 (5 : ZMod 2546581993)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (1494473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (1494473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2546581993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_71
      · exact prime_sixteenN_1494473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2546581993) ^ 1273290996 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2546581993) ^ 848860664 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2546581993) ^ 35867352 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2546581993) ^ 1704 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2548927123 : Nat.Prime 2548927123 := by
  apply lucas_primality 2548927123 (2 : ZMod 2548927123)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (71, 1), (854771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (71, 1), (854771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2548927123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_71
      · exact prime_sixteenN_854771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2548927123) ^ 1274463561 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 849642374 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 364132446 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 35900382 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 2982 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3100621319 : Nat.Prime 3100621319 := by
  apply lucas_primality 3100621319 (11 : ZMod 3100621319)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19073, 1), (81283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19073, 1), (81283, 1)] : List FactorBlock).map factorBlockValue).prod) = 3100621319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_19073
      · exact prime_sixteenN_81283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3100621319) ^ 1550310659 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100621319) ^ 162566 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100621319) ^ 38146 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3640375391 : Nat.Prime 3640375391 := by
  apply lucas_primality 3640375391 (7 : ZMod 3640375391)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (364037539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (364037539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3640375391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_364037539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3640375391) ^ 1820187695 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3640375391) ^ 728075078 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3640375391) ^ 10 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_4652375513 : Nat.Prime 4652375513 := by
  apply lucas_primality 4652375513 (3 : ZMod 4652375513)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (167, 1), (173, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (167, 1), (173, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod) = 4652375513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_167
      · exact prime_sixteenN_173
      · exact prime_sixteenN_20129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4652375513) ^ 2326187756 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652375513) ^ 27858536 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652375513) ^ 26892344 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652375513) ^ 231128 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_5381573389 : Nat.Prime 5381573389 := by
  apply lucas_primality 5381573389 (2 : ZMod 5381573389)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod) = 5381573389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2837
      · exact prime_sixteenN_158077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5381573389) ^ 2690786694 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1793857796 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1896924 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 34044 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_5411288681 : Nat.Prime 5411288681 := by
  apply lucas_primality 5411288681 (3 : ZMod 5411288681)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) = 5411288681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_241
      · exact prime_sixteenN_80191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5411288681) ^ 2705644340 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 1082257736 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 773041240 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 22453480 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 67480 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_7062967943 : Nat.Prime 7062967943 := by
  apply lucas_primality 7062967943 (5 : ZMod 7062967943)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) = 7062967943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5479
      · exact prime_sixteenN_644549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7062967943) ^ 3531483971 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 1289098 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 10958 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_7522921261 : Nat.Prime 7522921261 := by
  apply lucas_primality 7522921261 (2 : ZMod 7522921261)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (59, 1), (41669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (59, 1), (41669, 1)] : List FactorBlock).map factorBlockValue).prod) = 7522921261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_17
      · exact prime_sixteenN_59
      · exact prime_sixteenN_41669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7522921261) ^ 3761460630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522921261) ^ 2507640420 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522921261) ^ 1504584252 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522921261) ^ 442524780 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522921261) ^ 127507140 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522921261) ^ 180540 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_7647016217 : Nat.Prime 7647016217 := by
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_7549
      · exact prime_sixteenN_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7647016217) ^ 3823508108 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1092430888 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1012984 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 422744 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_8784511289 : Nat.Prime 8784511289 := by
  apply lucas_primality 8784511289 (3 : ZMod 8784511289)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8784511289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_37
      · exact prime_sixteenN_53
      · exact prime_sixteenN_167
      · exact prime_sixteenN_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8784511289) ^ 4392255644 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 1254930184 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 237419224 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 165745496 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 52601864 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 18339272 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_10892708831 : Nat.Prime 10892708831 := by
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_43
      · exact prime_sixteenN_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10892708831) ^ 5446354415 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 2178541766 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 253318810 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 430 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11527331273 : Nat.Prime 11527331273 := by
  apply lucas_primality 11527331273 (3 : ZMod 11527331273)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) = 11527331273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_1440916409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11527331273) ^ 5763665636 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11527331273) ^ 8 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_12049422601 : Nat.Prime 12049422601 := by
  apply lucas_primality 12049422601 (7 : ZMod 12049422601)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (20082371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (20082371, 1)] : List FactorBlock).map factorBlockValue).prod) = 12049422601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_20082371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12049422601) ^ 6024711300 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12049422601) ^ 4016474200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12049422601) ^ 2409884520 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 12049422601) ^ 600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_12863390587 : Nat.Prime 12863390587 := by
  apply lucas_primality 12863390587 (2 : ZMod 12863390587)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2143898431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2143898431, 1)] : List FactorBlock).map factorBlockValue).prod) = 12863390587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2143898431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12863390587) ^ 6431695293 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12863390587) ^ 4287796862 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 12863390587) ^ 6 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_13053027349 : Nat.Prime 13053027349 := by
  apply lucas_primality 13053027349 (2 : ZMod 13053027349)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) = 13053027349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_1511
      · exact prime_sixteenN_239963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13053027349) ^ 6526513674 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 4351009116 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 8638668 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 54396 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_14737656217 : Nat.Prime 14737656217 := by
  apply lucas_primality 14737656217 (10 : ZMod 14737656217)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) = 14737656217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_4129
      · exact prime_sixteenN_148721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 14737656217) ^ 7368828108 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 4912552072 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 3569304 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 99096 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_15040590709 : Nat.Prime 15040590709 := by
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_311
      · exact prime_sixteenN_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15040590709) ^ 7520295354 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 5013530236 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1367326428 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1156968516 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 48362028 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 533676 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_15274007543 : Nat.Prime 15274007543 := by
  apply lucas_primality 15274007543 (5 : ZMod 15274007543)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (3877, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (3877, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) = 15274007543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_181
      · exact prime_sixteenN_3877
      · exact prime_sixteenN_10883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15274007543) ^ 7637003771 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15274007543) ^ 84386782 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15274007543) ^ 3939646 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 15274007543) ^ 1403474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_17390803669 : Nat.Prime 17390803669 := by
  apply lucas_primality 17390803669 (6 : ZMod 17390803669)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (207033377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (207033377, 1)] : List FactorBlock).map factorBlockValue).prod) = 17390803669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_207033377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17390803669) ^ 8695401834 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17390803669) ^ 5796934556 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17390803669) ^ 2484400524 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17390803669) ^ 84 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_17482299607 : Nat.Prime 17482299607 := by
  apply lucas_primality 17482299607 (3 : ZMod 17482299607)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (323746289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (323746289, 1)] : List FactorBlock).map factorBlockValue).prod) = 17482299607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_323746289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17482299607) ^ 8741149803 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 17482299607) ^ 5827433202 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 17482299607) ^ 54 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_31
      · exact prime_sixteenN_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_20781589781 : Nat.Prime 20781589781 := by
  apply lucas_primality 20781589781 (11 : ZMod 20781589781)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (941, 1), (157747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (941, 1), (157747, 1)] : List FactorBlock).map factorBlockValue).prod) = 20781589781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_941
      · exact prime_sixteenN_157747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20781589781) ^ 10390794890 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 20781589781) ^ 4156317956 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 20781589781) ^ 2968798540 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 20781589781) ^ 22084580 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 20781589781) ^ 131740 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_20785154287 : Nat.Prime 20785154287 := by
  apply lucas_primality 20785154287 (3 : ZMod 20785154287)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) = 20785154287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_266476337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20785154287) ^ 10392577143 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 6928384762 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 1598858022 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 78 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_23959559521 : Nat.Prime 23959559521 := by
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_13
      · exact prime_sixteenN_191
      · exact prime_sixteenN_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23959559521) ^ 11979779760 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 7986519840 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 4791911904 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 1843043040 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 125442720 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 3575520 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_25846171151 : Nat.Prime 25846171151 := by
  apply lucas_primality 25846171151 (11 : ZMod 25846171151)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (516923423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (516923423, 1)] : List FactorBlock).map factorBlockValue).prod) = 25846171151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_516923423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 25846171151) ^ 12923085575 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25846171151) ^ 5169234230 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25846171151) ^ 50 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_26620044299 : Nat.Prime 26620044299 := by
  apply lucas_primality 26620044299 (2 : ZMod 26620044299)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) = 26620044299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_29
      · exact prime_sixteenN_67
      · exact prime_sixteenN_6850243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26620044299) ^ 13310022149 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 917932562 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 397314094 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 3886 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_28271170691 : Nat.Prime 28271170691 := by
  apply lucas_primality 28271170691 (6 : ZMod 28271170691)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (1889, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (1889, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) = 28271170691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_47
      · exact prime_sixteenN_1889
      · exact prime_sixteenN_4549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 28271170691) ^ 14135585345 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 28271170691) ^ 5654234138 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 28271170691) ^ 4038738670 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 28271170691) ^ 601514270 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 28271170691) ^ 14966210 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 28271170691) ^ 6214810 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_30384297329 : Nat.Prime 30384297329 := by
  apply lucas_primality 30384297329 (3 : ZMod 30384297329)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) = 30384297329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_1709
      · exact prime_sixteenN_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30384297329) ^ 15192148664 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 4340613904 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2762208848 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 17778992 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2105488 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_36733885319 : Nat.Prime 36733885319 := by
  apply lucas_primality 36733885319 (19 : ZMod 36733885319)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1979, 1), (713917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1979, 1), (713917, 1)] : List FactorBlock).map factorBlockValue).prod) = 36733885319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_13
      · exact prime_sixteenN_1979
      · exact prime_sixteenN_713917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 36733885319) ^ 18366942659 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 36733885319) ^ 2825683486 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 36733885319) ^ 18561842 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (19 : ZMod 36733885319) ^ 51454 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_151
      · exact prime_sixteenN_479
      · exact prime_sixteenN_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_48496315849 : Nat.Prime 48496315849 := by
  apply lucas_primality 48496315849 (26 : ZMod 48496315849)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2020679827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2020679827, 1)] : List FactorBlock).map factorBlockValue).prod) = 48496315849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2020679827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (26 : ZMod 48496315849) ^ 24248157924 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (26 : ZMod 48496315849) ^ 16165438616 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (26 : ZMod 48496315849) ^ 24 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_53761219979 : Nat.Prime 53761219979 := by
  apply lucas_primality 53761219979 (2 : ZMod 53761219979)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (641, 1), (5801, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (641, 1), (5801, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) = 53761219979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_641
      · exact prime_sixteenN_5801
      · exact prime_sixteenN_7229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53761219979) ^ 26880609989 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53761219979) ^ 83870858 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53761219979) ^ 9267578 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 53761219979) ^ 7436882 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_54675980063 : Nat.Prime 54675980063 := by
  apply lucas_primality 54675980063 (5 : ZMod 54675980063)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) = 54675980063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_61
      · exact prime_sixteenN_197
      · exact prime_sixteenN_206813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54675980063) ^ 27337990031 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 4970543642 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 896327542 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 277543046 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 264374 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_60083373169 : Nat.Prime 60083373169 := by
  apply lucas_primality 60083373169 (11 : ZMod 60083373169)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 60083373169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_31
      · exact prime_sixteenN_353
      · exact prime_sixteenN_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 60083373169) ^ 30041686584 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 20027791056 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 8583339024 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 4621797936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 1938173328 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 170207856 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 143397072 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_64859654689 : Nat.Prime 64859654689 := by
  apply lucas_primality 64859654689 (13 : ZMod 64859654689)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13291, 1), (50833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13291, 1), (50833, 1)] : List FactorBlock).map factorBlockValue).prod) = 64859654689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13291
      · exact prime_sixteenN_50833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 64859654689) ^ 32429827344 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 64859654689) ^ 21619884896 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 64859654689) ^ 4879968 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 64859654689) ^ 1275936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_76085543257 : Nat.Prime 76085543257 := by
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2221
      · exact prime_sixteenN_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76085543257) ^ 38042771628 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 25361847752 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 34257336 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 53304 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_78749395507 : Nat.Prime 78749395507 := by
  apply lucas_primality 78749395507 (2 : ZMod 78749395507)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1458322139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1458322139, 1)] : List FactorBlock).map factorBlockValue).prod) = 78749395507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_1458322139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78749395507) ^ 39374697753 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 78749395507) ^ 26249798502 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 78749395507) ^ 54 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_81828853627 : Nat.Prime 81828853627 := by
  apply lucas_primality 81828853627 (2 : ZMod 81828853627)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (719, 1), (85829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (719, 1), (85829, 1)] : List FactorBlock).map factorBlockValue).prod) = 81828853627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_719
      · exact prime_sixteenN_85829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81828853627) ^ 40914426813 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 81828853627) ^ 27276284542 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 81828853627) ^ 6294527202 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 81828853627) ^ 4813461978 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 81828853627) ^ 113809254 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 81828853627) ^ 953394 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_82299631397 : Nat.Prime 82299631397 := by
  apply lucas_primality 82299631397 (2 : ZMod 82299631397)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod) = 82299631397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_29
      · exact prime_sixteenN_41734093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82299631397) ^ 41149815698 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 4841154788 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 2837918324 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 1972 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_86986220647 : Nat.Prime 86986220647 := by
  apply lucas_primality 86986220647 (3 : ZMod 86986220647)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1115207957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1115207957, 1)] : List FactorBlock).map factorBlockValue).prod) = 86986220647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_1115207957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86986220647) ^ 43493110323 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 86986220647) ^ 28995406882 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 86986220647) ^ 6691247742 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 86986220647) ^ 78 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_132501777739 : Nat.Prime 132501777739 := by
  apply lucas_primality 132501777739 (3 : ZMod 132501777739)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 132501777739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_8747
      · exact prime_sixteenN_229519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132501777739) ^ 66250888869 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 44167259246 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 12045616158 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 15148254 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 577302 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_135031325183 : Nat.Prime 135031325183 := by
  apply lucas_primality 135031325183 (5 : ZMod 135031325183)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (449, 1), (11566843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (449, 1), (11566843, 1)] : List FactorBlock).map factorBlockValue).prod) = 135031325183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_13
      · exact prime_sixteenN_449
      · exact prime_sixteenN_11566843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 135031325183) ^ 67515662591 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 10387025014 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 300737918 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 11674 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_11
      · exact prime_sixteenN_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_142155846871 : Nat.Prime 142155846871 := by
  apply lucas_primality 142155846871 (3 : ZMod 142155846871)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (53, 1), (2579, 1), (34667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (53, 1), (2579, 1), (34667, 1)] : List FactorBlock).map factorBlockValue).prod) = 142155846871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_53
      · exact prime_sixteenN_2579
      · exact prime_sixteenN_34667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 142155846871) ^ 71077923435 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 142155846871) ^ 47385282290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 142155846871) ^ 28431169374 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 142155846871) ^ 2682185790 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 142155846871) ^ 55120530 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 142155846871) ^ 4100610 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_152895766423 : Nat.Prime 152895766423 := by
  apply lucas_primality 152895766423 (3 : ZMod 152895766423)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3640375391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3640375391, 1)] : List FactorBlock).map factorBlockValue).prod) = 152895766423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_3640375391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152895766423) ^ 76447883211 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 50965255474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 21842252346 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 42 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_159097227851 : Nat.Prime 159097227851 := by
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_11
      · exact prime_sixteenN_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159097227851) ^ 79548613925 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 31819445570 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 14463384350 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 550 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_160736592539 : Nat.Prime 160736592539 := by
  apply lucas_primality 160736592539 (2 : ZMod 160736592539)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod) = 160736592539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_29
      · exact prime_sixteenN_49627
      · exact prime_sixteenN_55843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160736592539) ^ 80368296269 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 5542641122 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 3238894 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 2878366 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_234103828649 : Nat.Prime 234103828649 := by
  apply lucas_primality 234103828649 (3 : ZMod 234103828649)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod) = 234103828649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_83
      · exact prime_sixteenN_307381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 234103828649) ^ 117051914324 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 7551736408 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 6327130504 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 2820528056 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 761608 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_321473185079 : Nat.Prime 321473185079 := by
  apply lucas_primality 321473185079 (7 : ZMod 321473185079)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod) = 321473185079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_160736592539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 321473185079) ^ 160736592539 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 321473185079) ^ 2 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_344256547937 : Nat.Prime 344256547937 := by
  apply lucas_primality 344256547937 (3 : ZMod 344256547937)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2467, 1), (622967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2467, 1), (622967, 1)] : List FactorBlock).map factorBlockValue).prod) = 344256547937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_2467
      · exact prime_sixteenN_622967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 344256547937) ^ 172128273968 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 49179506848 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 139544608 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 552608 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_390056504429 : Nat.Prime 390056504429 := by
  apply lucas_primality 390056504429 (2 : ZMod 390056504429)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) = 390056504429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_677
      · exact prime_sixteenN_144038591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390056504429) ^ 195028252214 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 576154364 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 2708 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_399877183627 : Nat.Prime 399877183627 := by
  apply lucas_primality 399877183627 (2 : ZMod 399877183627)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (1092560611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (1092560611, 1)] : List FactorBlock).map factorBlockValue).prod) = 399877183627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_61
      · exact prime_sixteenN_1092560611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 399877183627) ^ 199938591813 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 399877183627) ^ 133292394542 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 399877183627) ^ 6555363666 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 399877183627) ^ 366 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_430089759833 : Nat.Prime 430089759833 := by
  apply lucas_primality 430089759833 (3 : ZMod 430089759833)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53761219979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53761219979, 1)] : List FactorBlock).map factorBlockValue).prod) = 430089759833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_53761219979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 430089759833) ^ 215044879916 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 430089759833) ^ 8 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_441727989187 : Nat.Prime 441727989187 := by
  apply lucas_primality 441727989187 (3 : ZMod 441727989187)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (53, 1), (79, 1), (991, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (53, 1), (79, 1), (991, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) = 441727989187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_53
      · exact prime_sixteenN_79
      · exact prime_sixteenN_991
      · exact prime_sixteenN_1613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 441727989187) ^ 220863994593 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 147242663062 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 40157089926 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 8334490362 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 5591493534 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 445739646 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 441727989187) ^ 273854922 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_397
      · exact prime_sixteenN_2531
      · exact prime_sixteenN_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_493797788383 : Nat.Prime 493797788383 := by
  apply lucas_primality 493797788383 (3 : ZMod 493797788383)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod) = 493797788383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_82299631397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 493797788383) ^ 246898894191 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 164599262794 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 6 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_544862914369 : Nat.Prime 544862914369 := by
  apply lucas_primality 544862914369 (13 : ZMod 544862914369)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (67, 1), (42355637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (67, 1), (42355637, 1)] : List FactorBlock).map factorBlockValue).prod) = 544862914369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_67
      · exact prime_sixteenN_42355637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 544862914369) ^ 272431457184 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 544862914369) ^ 181620971456 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 544862914369) ^ 8132282304 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 544862914369) ^ 12864 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_545479341709 : Nat.Prime 545479341709 := by
  apply lucas_primality 545479341709 (10 : ZMod 545479341709)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (41, 1), (158385407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (41, 1), (158385407, 1)] : List FactorBlock).map factorBlockValue).prod) = 545479341709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_41
      · exact prime_sixteenN_158385407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 545479341709) ^ 272739670854 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 545479341709) ^ 181826447236 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 545479341709) ^ 77925620244 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 545479341709) ^ 13304374188 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 545479341709) ^ 3444 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_592603554899 : Nat.Prime 592603554899 := by
  apply lucas_primality 592603554899 (2 : ZMod 592603554899)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (1239756391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (1239756391, 1)] : List FactorBlock).map factorBlockValue).prod) = 592603554899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_239
      · exact prime_sixteenN_1239756391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 592603554899) ^ 296301777449 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 592603554899) ^ 2479512782 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 592603554899) ^ 478 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_739
      · exact prime_sixteenN_1307
      · exact prime_sixteenN_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1272241326337 : Nat.Prime 1272241326337 := by
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1272241326337) ^ 636120663168 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 424080442112 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 768 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_35279
      · exact prime_sixteenN_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1982473007243 : Nat.Prime 1982473007243 := by
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1982473007243) ^ 991236503621 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 283210429606 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 152497923634 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 182 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2017561841483 : Nat.Prime 2017561841483 := by
  apply lucas_primality 2017561841483 (2 : ZMod 2017561841483)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (41, 1), (211, 1), (10600781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (41, 1), (211, 1), (10600781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2017561841483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_41
      · exact prime_sixteenN_211
      · exact prime_sixteenN_10600781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2017561841483) ^ 1008780920741 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017561841483) ^ 183414712862 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017561841483) ^ 49208825402 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017561841483) ^ 9561904462 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017561841483) ^ 190322 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2024581991983 : Nat.Prime 2024581991983 := by
  apply lucas_primality 2024581991983 (3 : ZMod 2024581991983)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2024581991983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_6997
      · exact prime_sixteenN_4384091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2024581991983) ^ 1012290995991 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 674860663994 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 184052908362 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 289350006 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 461802 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_23
      · exact prime_sixteenN_9739
      · exact prime_sixteenN_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2329141311671 : Nat.Prime 2329141311671 := by
  apply lucas_primality 2329141311671 (11 : ZMod 2329141311671)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329141311671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_107
      · exact prime_sixteenN_5413
      · exact prime_sixteenN_402137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2329141311671) ^ 1164570655835 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 465828262334 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 21767675810 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 430286590 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 5791910 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2943508165337 : Nat.Prime 2943508165337 := by
  apply lucas_primality 2943508165337 (3 : ZMod 2943508165337)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (59, 1), (509, 1), (231169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (59, 1), (509, 1), (231169, 1)] : List FactorBlock).map factorBlockValue).prod) = 2943508165337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_509
      · exact prime_sixteenN_231169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2943508165337) ^ 1471754082668 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2943508165337) ^ 55537889912 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2943508165337) ^ 49889968904 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2943508165337) ^ 5782923704 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2943508165337) ^ 12733144 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3122914114891 : Nat.Prime 3122914114891 := by
  apply lucas_primality 3122914114891 (3 : ZMod 3122914114891)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (109, 1), (1693, 1), (3187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (109, 1), (1693, 1), (3187, 1)] : List FactorBlock).map factorBlockValue).prod) = 3122914114891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_59
      · exact prime_sixteenN_109
      · exact prime_sixteenN_1693
      · exact prime_sixteenN_3187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3122914114891) ^ 1561457057445 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 1040971371630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 624582822978 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 52930747710 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 28650588210 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 1844603730 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3122914114891) ^ 979891470 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_4167738550189 : Nat.Prime 4167738550189 := by
  apply lucas_primality 4167738550189 (6 : ZMod 4167738550189)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (12863390587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (12863390587, 1)] : List FactorBlock).map factorBlockValue).prod) = 4167738550189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_12863390587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4167738550189) ^ 2083869275094 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4167738550189) ^ 1389246183396 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4167738550189) ^ 324 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_4287731098507 : Nat.Prime 4287731098507 := by
  apply lucas_primality 4287731098507 (2 : ZMod 4287731098507)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287731098507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_61
      · exact prime_sixteenN_167
      · exact prime_sixteenN_70150373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4287731098507) ^ 2143865549253 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 1429243699502 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 70290673746 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 25675036518 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 61122 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_4658282623343 : Nat.Prime 4658282623343 := by
  apply lucas_primality 4658282623343 (5 : ZMod 4658282623343)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658282623343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_2329141311671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4658282623343) ^ 2329141311671 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4658282623343) ^ 2 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_4937977883831 : Nat.Prime 4937977883831 := by
  apply lucas_primality 4937977883831 (11 : ZMod 4937977883831)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod) = 4937977883831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_493797788383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4937977883831) ^ 2468988941915 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 987595576766 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 10 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_5934672374047 : Nat.Prime 5934672374047 := by
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934672374047) ^ 2967336187023 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 1978224124682 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 456513259542 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 78 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_7938446047463 : Nat.Prime 7938446047463 := by
  apply lucas_primality 7938446047463 (5 : ZMod 7938446047463)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (2789, 1), (7010693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (2789, 1), (7010693, 1)] : List FactorBlock).map factorBlockValue).prod) = 7938446047463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_29
      · exact prime_sixteenN_2789
      · exact prime_sixteenN_7010693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7938446047463) ^ 3969223023731 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7938446047463) ^ 1134063721066 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7938446047463) ^ 273739518878 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7938446047463) ^ 2846341358 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7938446047463) ^ 1132334 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_8215068638333 : Nat.Prime 8215068638333 := by
  apply lucas_primality 8215068638333 (2 : ZMod 8215068638333)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (937, 1), (75581171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (937, 1), (75581171, 1)] : List FactorBlock).map factorBlockValue).prod) = 8215068638333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_29
      · exact prime_sixteenN_937
      · exact prime_sixteenN_75581171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8215068638333) ^ 4107534319166 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 283278228908 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 8767415836 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 108692 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_8402550447737 : Nat.Prime 8402550447737 := by
  apply lucas_primality 8402550447737 (3 : ZMod 8402550447737)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) = 8402550447737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_381761
      · exact prime_sixteenN_2751247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8402550447737) ^ 4201275223868 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 22009976 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 3054088 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_10310435557003 : Nat.Prime 10310435557003 := by
  apply lucas_primality 10310435557003 (3 : ZMod 10310435557003)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (81828853627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (81828853627, 1)] : List FactorBlock).map factorBlockValue).prod) = 10310435557003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_81828853627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10310435557003) ^ 5155217778501 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10310435557003) ^ 3436811852334 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10310435557003) ^ 1472919365286 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10310435557003) ^ 126 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11012157741281 : Nat.Prime 11012157741281 := by
  apply lucas_primality 11012157741281 (3 : ZMod 11012157741281)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) = 11012157741281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_31
      · exact prime_sixteenN_137
      · exact prime_sixteenN_16205789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11012157741281) ^ 5506078870640 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 2202431548256 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 355230894880 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 80380713440 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 679520 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11680677399577 : Nat.Prime 11680677399577 := by
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_23
      · exact prime_sixteenN_79
      · exact prime_sixteenN_397
      · exact prime_sixteenN_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11680677399577) ^ 5840338699788 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 3893559133192 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 507855539112 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 147856675944 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 29422361208 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 17312376 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_12550654586551 : Nat.Prime 12550654586551 := by
  apply lucas_primality 12550654586551 (6 : ZMod 12550654586551)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) = 12550654586551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_66553
      · exact prime_sixteenN_1257209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12550654586551) ^ 6275327293275 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 4183551528850 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 2510130917310 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 188581350 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 9982950 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_13424731660273 : Nat.Prime 13424731660273 := by
  apply lucas_primality 13424731660273 (5 : ZMod 13424731660273)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) = 13424731660273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_379
      · exact prime_sixteenN_907
      · exact prime_sixteenN_813613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13424731660273) ^ 6712365830136 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 4474910553424 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 35421455568 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 14801247696 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 16500144 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_13443454509487 : Nat.Prime 13443454509487 := by
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_293
      · exact prime_sixteenN_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13443454509487) ^ 6721727254743 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 4481151503162 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 45882097302 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 1758 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_18150091583623 : Nat.Prime 18150091583623 := by
  apply lucas_primality 18150091583623 (3 : ZMod 18150091583623)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (28271170691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (28271170691, 1)] : List FactorBlock).map factorBlockValue).prod) = 18150091583623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_107
      · exact prime_sixteenN_28271170691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18150091583623) ^ 9075045791811 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18150091583623) ^ 6050030527874 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18150091583623) ^ 169627024146 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18150091583623) ^ 642 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_20782640965039 : Nat.Prime 20782640965039 := by
  apply lucas_primality 20782640965039 (3 : ZMod 20782640965039)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod) = 20782640965039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_35461
      · exact prime_sixteenN_97678393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20782640965039) ^ 10391320482519 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 6927546988346 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 586070358 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 212766 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_27351922138837 : Nat.Prime 27351922138837 := by
  apply lucas_primality 27351922138837 (2 : ZMod 27351922138837)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (48496315849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (48496315849, 1)] : List FactorBlock).map factorBlockValue).prod) = 27351922138837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_47
      · exact prime_sixteenN_48496315849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27351922138837) ^ 13675961069418 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27351922138837) ^ 9117307379612 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27351922138837) ^ 581955790188 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27351922138837) ^ 564 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_43209229447187 : Nat.Prime 43209229447187 := by
  apply lucas_primality 43209229447187 (2 : ZMod 43209229447187)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (163, 1), (12049422601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (163, 1), (12049422601, 1)] : List FactorBlock).map factorBlockValue).prod) = 43209229447187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_163
      · exact prime_sixteenN_12049422601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43209229447187) ^ 21604614723593 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 43209229447187) ^ 3928111767926 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 43209229447187) ^ 265087297222 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 43209229447187) ^ 3586 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_45820001621089 : Nat.Prime 45820001621089 := by
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 45820001621089) ^ 22910000810544 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 15273333873696 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 288 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_89
      · exact prime_sixteenN_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_68453114335699 : Nat.Prime 68453114335699 := by
  apply lucas_primality 68453114335699 (7 : ZMod 68453114335699)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (491, 1), (30071, 1), (772703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (491, 1), (30071, 1), (772703, 1)] : List FactorBlock).map factorBlockValue).prod) = 68453114335699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_491
      · exact prime_sixteenN_30071
      · exact prime_sixteenN_772703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 68453114335699) ^ 34226557167849 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 68453114335699) ^ 22817704778566 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 68453114335699) ^ 139415711478 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 68453114335699) ^ 2276383038 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 68453114335699) ^ 88589166 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_73650013801457 : Nat.Prime 73650013801457 := by
  apply lucas_primality 73650013801457 (3 : ZMod 73650013801457)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1627, 1), (5987, 1), (472559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1627, 1), (5987, 1), (472559, 1)] : List FactorBlock).map factorBlockValue).prod) = 73650013801457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_1627
      · exact prime_sixteenN_5987
      · exact prime_sixteenN_472559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73650013801457) ^ 36825006900728 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 73650013801457) ^ 45267371728 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 73650013801457) ^ 12301655888 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 73650013801457) ^ 155853584 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_74050722409721 : Nat.Prime 74050722409721 := by
  apply lucas_primality 74050722409721 (6 : ZMod 74050722409721)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) = 74050722409721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_15131
      · exact prime_sixteenN_17478479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74050722409721) ^ 37025361204860 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 14810144481944 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 10578674629960 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4893974120 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4236680 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_98372345516581 : Nat.Prime 98372345516581 := by
  apply lucas_primality 98372345516581 (2 : ZMod 98372345516581)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod) = 98372345516581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_103393
      · exact prime_sixteenN_15857351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98372345516581) ^ 49186172758290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 32790781838860 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 19674469103316 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 951441060 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 6203580 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_118447369355363 : Nat.Prime 118447369355363 := by
  apply lucas_primality 118447369355363 (2 : ZMod 118447369355363)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1217, 1), (685403783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1217, 1), (685403783, 1)] : List FactorBlock).map factorBlockValue).prod) = 118447369355363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_71
      · exact prime_sixteenN_1217
      · exact prime_sixteenN_685403783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118447369355363) ^ 59223684677681 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118447369355363) ^ 1668272807822 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118447369355363) ^ 97327337186 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 118447369355363) ^ 172814 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_128096483851537 : Nat.Prime 128096483851537 := by
  apply lucas_primality 128096483851537 (10 : ZMod 128096483851537)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) = 128096483851537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_499
      · exact prime_sixteenN_647
      · exact prime_sixteenN_8265919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 128096483851537) ^ 64048241925768 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 42698827950512 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 256706380464 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 197985291888 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 15496944 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_167832428999197 : Nat.Prime 167832428999197 := by
  apply lucas_primality 167832428999197 (2 : ZMod 167832428999197)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) = 167832428999197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_73
      · exact prime_sixteenN_14737656217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167832428999197) ^ 83916214499598 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 55944142999732 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 12910186846092 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 2299074369852 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 11388 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_284731330549429 : Nat.Prime 284731330549429 := by
  apply lucas_primality 284731330549429 (2 : ZMod 284731330549429)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) = 284731330549429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_67
      · exact prime_sixteenN_4441
      · exact prime_sixteenN_1265779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 284731330549429) ^ 142365665274714 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 94910443516476 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 40675904364204 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 4249721351484 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 64114237908 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 224945532 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_289817799176999 : Nat.Prime 289817799176999 := by
  apply lucas_primality 289817799176999 (7 : ZMod 289817799176999)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) = 289817799176999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_61
      · exact prime_sixteenN_439
      · exact prime_sixteenN_5411288681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 289817799176999) ^ 144908899588499 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 4751111461918 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 660177219082 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 53558 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_324419281478407 : Nat.Prime 324419281478407 := by
  apply lucas_primality 324419281478407 (3 : ZMod 324419281478407)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (773, 1), (911, 1), (25593889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (773, 1), (911, 1), (25593889, 1)] : List FactorBlock).map factorBlockValue).prod) = 324419281478407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_773
      · exact prime_sixteenN_911
      · exact prime_sixteenN_25593889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 324419281478407) ^ 162209640739203 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 324419281478407) ^ 108139760492802 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 324419281478407) ^ 419688591822 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 324419281478407) ^ 356113371546 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 324419281478407) ^ 12675654 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_375536651467739 : Nat.Prime 375536651467739 := by
  apply lucas_primality 375536651467739 (2 : ZMod 375536651467739)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1578281, 1), (118970149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1578281, 1), (118970149, 1)] : List FactorBlock).map factorBlockValue).prod) = 375536651467739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_1578281
      · exact prime_sixteenN_118970149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 375536651467739) ^ 187768325733869 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 375536651467739) ^ 237940298 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 375536651467739) ^ 3156562 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_416726749916363 : Nat.Prime 416726749916363 := by
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_4787
      · exact prime_sixteenN_8839
      · exact prime_sixteenN_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416726749916363) ^ 208363374958181 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 87053843726 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 47146368358 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 84624586 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_67
      · exact prime_sixteenN_28807
      · exact prime_sixteenN_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_522414067849459 : Nat.Prime 522414067849459 := by
  apply lucas_primality 522414067849459 (2 : ZMod 522414067849459)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) = 522414067849459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_59
      · exact prime_sixteenN_71
      · exact prime_sixteenN_20785154287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 522414067849459) ^ 261207033924729 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 174138022616486 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 8854475726262 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 7357944617598 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 25134 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_1123
      · exact prime_sixteenN_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_700505369226119 : Nat.Prime 700505369226119 := by
  apply lucas_primality 700505369226119 (7 : ZMod 700505369226119)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod) = 700505369226119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_173
      · exact prime_sixteenN_2024581991983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 700505369226119) ^ 350252684613059 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 4049163983966 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 346 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1276216592026469 : Nat.Prime 1276216592026469 := by
  apply lucas_primality 1276216592026469 (2 : ZMod 1276216592026469)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276216592026469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_293081
      · exact prime_sixteenN_1088621057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1276216592026469) ^ 638108296013234 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 4354484228 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 1172324 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1426018778793047 : Nat.Prime 1426018778793047 := by
  apply lucas_primality 1426018778793047 (5 : ZMod 1426018778793047)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426018778793047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11867
      · exact prime_sixteenN_60083373169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1426018778793047) ^ 713009389396523 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 120166746338 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 23734 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1569947948827553 : Nat.Prime 1569947948827553 := by
  apply lucas_primality 1569947948827553 (3 : ZMod 1569947948827553)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (89, 1), (78749395507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (89, 1), (78749395507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569947948827553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_89
      · exact prime_sixteenN_78749395507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1569947948827553) ^ 784973974413776 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 224278278403936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 17639864593568 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 19936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_41
      · exact prime_sixteenN_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1946515688870443 : Nat.Prime 1946515688870443 := by
  apply lucas_primality 1946515688870443 (2 : ZMod 1946515688870443)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (324419281478407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (324419281478407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1946515688870443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_324419281478407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1946515688870443) ^ 973257844435221 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946515688870443) ^ 648838562956814 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946515688870443) ^ 6 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3158115935550403 : Nat.Prime 3158115935550403 := by
  apply lucas_primality 3158115935550403 (2 : ZMod 3158115935550403)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (18150091583623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (18150091583623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3158115935550403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_29
      · exact prime_sixteenN_18150091583623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3158115935550403) ^ 1579057967775201 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158115935550403) ^ 1052705311850134 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158115935550403) ^ 108900549501738 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158115935550403) ^ 174 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_9691183070205617 : Nat.Prime 9691183070205617 := by
  apply lucas_primality 9691183070205617 (3 : ZMod 9691183070205617)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) = 9691183070205617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_12251
      · exact prime_sixteenN_7062967943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9691183070205617) ^ 4845591535102808 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1384454724315088 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 791052409616 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1372112 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_9866893336187777 : Nat.Prime 9866893336187777 := by
  apply lucas_primality 9866893336187777 (3 : ZMod 9866893336187777)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866893336187777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11012157741281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9866893336187777) ^ 4933446668093888 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 1409556190883968 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 896 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11471261097382837 : Nat.Prime 11471261097382837 := by
  apply lucas_primality 11471261097382837 (2 : ZMod 11471261097382837)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1703843, 1), (561048421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1703843, 1), (561048421, 1)] : List FactorBlock).map factorBlockValue).prod) = 11471261097382837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_1703843
      · exact prime_sixteenN_561048421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11471261097382837) ^ 5735630548691418 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11471261097382837) ^ 3823753699127612 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11471261097382837) ^ 6732581052 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11471261097382837) ^ 20446116 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11952932392200829 : Nat.Prime 11952932392200829 := by
  apply lucas_primality 11952932392200829 (11 : ZMod 11952932392200829)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (45893, 1), (3100621319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (45893, 1), (3100621319, 1)] : List FactorBlock).map factorBlockValue).prod) = 11952932392200829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_45893
      · exact prime_sixteenN_3100621319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11952932392200829) ^ 5976466196100414 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11952932392200829) ^ 3984310797400276 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11952932392200829) ^ 1707561770314404 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11952932392200829) ^ 260452190796 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 11952932392200829) ^ 3855012 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_15205887258860777 : Nat.Prime 15205887258860777 := by
  apply lucas_primality 15205887258860777 (3 : ZMod 15205887258860777)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (21851, 1), (86986220647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (21851, 1), (86986220647, 1)] : List FactorBlock).map factorBlockValue).prod) = 15205887258860777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_21851
      · exact prime_sixteenN_86986220647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15205887258860777) ^ 7602943629430388 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205887258860777) ^ 695889765176 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205887258860777) ^ 174808 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_384973
      · exact prime_sixteenN_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_31507000248526559 : Nat.Prime 31507000248526559 := by
  apply lucas_primality 31507000248526559 (7 : ZMod 31507000248526559)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (118447369355363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (118447369355363, 1)] : List FactorBlock).map factorBlockValue).prod) = 31507000248526559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_19
      · exact prime_sixteenN_118447369355363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31507000248526559) ^ 15753500124263279 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31507000248526559) ^ 4501000035503794 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31507000248526559) ^ 1658263170975082 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 31507000248526559) ^ 266 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_42823345155149747 : Nat.Prime 42823345155149747 := by
  apply lucas_primality 42823345155149747 (2 : ZMod 42823345155149747)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1946515688870443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1946515688870443, 1)] : List FactorBlock).map factorBlockValue).prod) = 42823345155149747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_11
      · exact prime_sixteenN_1946515688870443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42823345155149747) ^ 21411672577574873 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42823345155149747) ^ 3893031377740886 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42823345155149747) ^ 22 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_71347522561263737 : Nat.Prime 71347522561263737 := by
  apply lucas_primality 71347522561263737 (3 : ZMod 71347522561263737)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) = 71347522561263737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_24581699
      · exact prime_sixteenN_362808133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71347522561263737) ^ 35673761280631868 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 2902465064 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 196653592 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_83606640482167961 : Nat.Prime 83606640482167961 := by
  apply lucas_primality 83606640482167961 (3 : ZMod 83606640482167961)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1213, 1), (3911, 1), (440587493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1213, 1), (3911, 1), (440587493, 1)] : List FactorBlock).map factorBlockValue).prod) = 83606640482167961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_1213
      · exact prime_sixteenN_3911
      · exact prime_sixteenN_440587493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83606640482167961) ^ 41803320241083980 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 83606640482167961) ^ 16721328096433592 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 83606640482167961) ^ 68925507404920 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 83606640482167961) ^ 21377305160360 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 83606640482167961) ^ 189761720 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_85512338798115589 : Nat.Prime 85512338798115589 := by
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_59
      · exact prime_sixteenN_71
      · exact prime_sixteenN_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85512338798115589) ^ 42756169399057794 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 28504112932705196 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1449361674544332 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1204399138001628 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 3569028 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_157899309577893787 : Nat.Prime 157899309577893787 := by
  apply lucas_primality 157899309577893787 (2 : ZMod 157899309577893787)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9042907, 1), (415741019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9042907, 1), (415741019, 1)] : List FactorBlock).map factorBlockValue).prod) = 157899309577893787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_9042907
      · exact prime_sixteenN_415741019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157899309577893787) ^ 78949654788946893 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 52633103192631262 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 22557044225413398 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 17461122798 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 379802094 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_168618696733348423 : Nat.Prime 168618696733348423 := by
  apply lucas_primality 168618696733348423 (3 : ZMod 168618696733348423)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (953, 1), (15667, 1), (171113017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (953, 1), (15667, 1), (171113017, 1)] : List FactorBlock).map factorBlockValue).prod) = 168618696733348423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_11
      · exact prime_sixteenN_953
      · exact prime_sixteenN_15667
      · exact prime_sixteenN_171113017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 168618696733348423) ^ 84309348366674211 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 168618696733348423) ^ 56206232244449474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 168618696733348423) ^ 15328972430304402 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 168618696733348423) ^ 176934624064374 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 168618696733348423) ^ 10762666543266 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 168618696733348423) ^ 985422966 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_190813341386997503 : Nat.Prime 190813341386997503 := by
  apply lucas_primality 190813341386997503 (5 : ZMod 190813341386997503)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod) = 190813341386997503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_139
      · exact prime_sixteenN_4937977883831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190813341386997503) ^ 95406670693498751 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 1372757851705018 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 38642 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_5037757
      · exact prime_sixteenN_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_29
      · exact prime_sixteenN_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_61717
      · exact prime_sixteenN_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_597324387877913089 : Nat.Prime 597324387877913089 := by
  apply lucas_primality 597324387877913089 (23 : ZMod 597324387877913089)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (43209229447187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (43209229447187, 1)] : List FactorBlock).map factorBlockValue).prod) = 597324387877913089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_43209229447187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 597324387877913089) ^ 298662193938956544 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (23 : ZMod 597324387877913089) ^ 199108129292637696 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (23 : ZMod 597324387877913089) ^ 13824 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_668187974337575183 : Nat.Prime 668187974337575183 := by
  apply lucas_primality 668187974337575183 (5 : ZMod 668187974337575183)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (59, 1), (193, 1), (204361, 1), (3880249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (59, 1), (193, 1), (204361, 1), (3880249, 1)] : List FactorBlock).map factorBlockValue).prod) = 668187974337575183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_37
      · exact prime_sixteenN_59
      · exact prime_sixteenN_193
      · exact prime_sixteenN_204361
      · exact prime_sixteenN_3880249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 668187974337575183) ^ 334093987168787591 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 668187974337575183) ^ 18059134441556086 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 668187974337575183) ^ 11325219904026698 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 668187974337575183) ^ 3462113856671374 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 668187974337575183) ^ 3269645256862 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 668187974337575183) ^ 172202344318 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_710602504382600099 : Nat.Prime 710602504382600099 := by
  apply lucas_primality 710602504382600099 (2 : ZMod 710602504382600099)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) = 710602504382600099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_29
      · exact prime_sixteenN_73
      · exact prime_sixteenN_167832428999197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 710602504382600099) ^ 355301252191300049 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 24503534633882762 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 9734280881953426 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 4234 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3030158014634483503 : Nat.Prime 3030158014634483503 := by
  apply lucas_primality 3030158014634483503 (3 : ZMod 3030158014634483503)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod) = 3030158014634483503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_6514591
      · exact prime_sixteenN_143826233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3030158014634483503) ^ 1515079007317241751 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 1010052671544827834 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 432879716376354786 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 275468910421316682 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 465134037522 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 21068187294 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_6634509058759861109 : Nat.Prime 6634509058759861109 := by
  apply lucas_primality 6634509058759861109 (2 : ZMod 6634509058759861109)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) = 6634509058759861109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_59
      · exact prime_sixteenN_97
      · exact prime_sixteenN_289817799176999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6634509058759861109) ^ 3317254529379930554 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 112449306080675612 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 68397000605771764 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 22892 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_439
      · exact prime_sixteenN_853
      · exact prime_sixteenN_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_19
      · exact prime_sixteenN_1823
      · exact prime_sixteenN_3271
      · exact prime_sixteenN_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_13451362101445396397 : Nat.Prime 13451362101445396397 := by
  apply lucas_primality 13451362101445396397 (2 : ZMod 13451362101445396397)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) = 13451362101445396397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_347
      · exact prime_sixteenN_9691183070205617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13451362101445396397) ^ 6725681050722698198 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 38764732280822468 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 1388 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_23
      · exact prime_sixteenN_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_17672454355456607929 : Nat.Prime 17672454355456607929 := by
  apply lucas_primality 17672454355456607929 (7 : ZMod 17672454355456607929)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (83, 1), (709, 1), (743, 1), (1295475289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (83, 1), (709, 1), (743, 1), (1295475289, 1)] : List FactorBlock).map factorBlockValue).prod) = 17672454355456607929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_83
      · exact prime_sixteenN_709
      · exact prime_sixteenN_743
      · exact prime_sixteenN_1295475289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 17672454355456607929) ^ 8836227177728303964 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 5890818118485535976 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 1359419565804354456 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 212921136812730216 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 24925887666370392 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 23785268311516296 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 17672454355456607929) ^ 13641676152 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_28865922088264225807 : Nat.Prime 28865922088264225807 := by
  apply lucas_primality 28865922088264225807 (3 : ZMod 28865922088264225807)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) = 28865922088264225807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_821
      · exact prime_sixteenN_9124861
      · exact prime_sixteenN_642191821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28865922088264225807) ^ 14432961044132112903 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 9621974029421408602 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 35159466611771286 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 3163436910246 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 44949065286 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_67945843775149768429 : Nat.Prime 67945843775149768429 := by
  apply lucas_primality 67945843775149768429 (2 : ZMod 67945843775149768429)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (3547, 1), (299287, 1), (761203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (3547, 1), (299287, 1), (761203, 1)] : List FactorBlock).map factorBlockValue).prod) = 67945843775149768429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_3547
      · exact prime_sixteenN_299287
      · exact prime_sixteenN_761203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67945843775149768429) ^ 33972921887574884214 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 22648614591716589476 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 9706549110735681204 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 6176894888649978948 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 5226603367319212956 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 19155862355553924 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 227025710355444 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 89261135039076 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_168550987212050609377 : Nat.Prime 168550987212050609377 := by
  apply lucas_primality 168550987212050609377 (5 : ZMod 168550987212050609377)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (83606640482167961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (83606640482167961, 1)] : List FactorBlock).map factorBlockValue).prod) = 168550987212050609377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_7
      · exact prime_sixteenN_83606640482167961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 168550987212050609377) ^ 84275493606025304688 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 168550987212050609377) ^ 56183662404016869792 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 168550987212050609377) ^ 24078712458864372768 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 168550987212050609377) ^ 2016 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_19
      · exact prime_sixteenN_107
      · exact prime_sixteenN_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2608698490372481172527 : Nat.Prime 2608698490372481172527 := by
  apply lucas_primality 2608698490372481172527 (5 : ZMod 2608698490372481172527)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 2), (9419, 1), (68453114335699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 2), (9419, 1), (68453114335699, 1)] : List FactorBlock).map factorBlockValue).prod) = 2608698490372481172527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_7
      · exact prime_sixteenN_17
      · exact prime_sixteenN_9419
      · exact prime_sixteenN_68453114335699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2608698490372481172527) ^ 1304349245186240586263 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2608698490372481172527) ^ 372671212910354453218 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2608698490372481172527) ^ 153452852374851833678 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2608698490372481172527) ^ 276961300602238154 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2608698490372481172527) ^ 38109274 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_67
      · exact prime_sixteenN_89
      · exact prime_sixteenN_467
      · exact prime_sixteenN_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_10225016416573823164327 : Nat.Prime 10225016416573823164327 := by
  apply lucas_primality 10225016416573823164327 (3 : ZMod 10225016416573823164327)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (37, 1), (233, 1), (15205887258860777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (37, 1), (233, 1), (15205887258860777, 1)] : List FactorBlock).map factorBlockValue).prod) = 10225016416573823164327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_13
      · exact prime_sixteenN_37
      · exact prime_sixteenN_233
      · exact prime_sixteenN_15205887258860777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10225016416573823164327) ^ 5112508208286911582163 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10225016416573823164327) ^ 3408338805524607721442 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10225016416573823164327) ^ 786539724351832551102 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10225016416573823164327) ^ 276351795042535761198 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10225016416573823164327) ^ 43884190629072202422 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 10225016416573823164327) ^ 672438 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_29
      · exact prime_sixteenN_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_16502686268178916959227 : Nat.Prime 16502686268178916959227 := by
  apply lucas_primality 16502686268178916959227 (2 : ZMod 16502686268178916959227)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (2732549, 1), (73650013801457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (2732549, 1), (73650013801457, 1)] : List FactorBlock).map factorBlockValue).prod) = 16502686268178916959227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_41
      · exact prime_sixteenN_2732549
      · exact prime_sixteenN_73650013801457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16502686268178916959227) ^ 8251343134089458479613 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16502686268178916959227) ^ 402504543126315047786 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16502686268178916959227) ^ 6039301131719474 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16502686268178916959227) ^ 224069018 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_29229349063912647400411 : Nat.Prime 29229349063912647400411 := by
  apply lucas_primality 29229349063912647400411 (12 : ZMod 29229349063912647400411)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (307, 1), (2029, 1), (8707, 1), (308134529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (307, 1), (2029, 1), (8707, 1), (308134529, 1)] : List FactorBlock).map factorBlockValue).prod) = 29229349063912647400411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_11
      · exact prime_sixteenN_53
      · exact prime_sixteenN_307
      · exact prime_sixteenN_2029
      · exact prime_sixteenN_8707
      · exact prime_sixteenN_308134529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 29229349063912647400411) ^ 14614674531956323700205 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 9743116354637549133470 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 5845869812782529480082 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 2657213551264786127310 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 551497152149295233970 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 95209606071376701630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 14405790568710028290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 3356994264834345630 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 94859051203290 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_34890825049700005681357 : Nat.Prime 34890825049700005681357 := by
  apply lucas_primality 34890825049700005681357 (2 : ZMod 34890825049700005681357)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod) = 34890825049700005681357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_2213
      · exact prime_sixteenN_244140209
      · exact prime_sixteenN_5381573389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34890825049700005681357) ^ 17445412524850002840678 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 11630275016566668560452 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 15766301423271579612 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 142913062918284 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 6483387390204 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_69349809527745966433433 : Nat.Prime 69349809527745966433433 := by
  apply lucas_primality 69349809527745966433433 (3 : ZMod 69349809527745966433433)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (23, 1), (36407143, 1), (544862914369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (23, 1), (36407143, 1), (544862914369, 1)] : List FactorBlock).map factorBlockValue).prod) = 69349809527745966433433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_36407143
      · exact prime_sixteenN_544862914369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69349809527745966433433) ^ 34674904763872983216716 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 69349809527745966433433) ^ 3649989975144524549128 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 69349809527745966433433) ^ 3015209109901998540584 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 69349809527745966433433) ^ 1904840748634024 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 69349809527745966433433) ^ 127279371928 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_3061
      · exact prime_sixteenN_61379
      · exact prime_sixteenN_382747
      · exact prime_sixteenN_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_938632965099248562505919 : Nat.Prime 938632965099248562505919 := by
  apply lucas_primality 938632965099248562505919 (7 : ZMod 938632965099248562505919)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) = 938632965099248562505919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3011
      · exact prime_sixteenN_15797
      · exact prime_sixteenN_9866893336187777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 938632965099248562505919) ^ 469316482549624281252959 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 311734628063516626538 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 59418431670522793094 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 95129534 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_5
      · exact prime_sixteenN_1321
      · exact prime_sixteenN_1255074433
      · exact prime_sixteenN_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1663261245550440189939487 : Nat.Prime 1663261245550440189939487 := by
  apply lucas_primality 1663261245550440189939487 (5 : ZMod 1663261245550440189939487)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (107, 1), (22421449, 1), (3122914114891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (107, 1), (22421449, 1), (3122914114891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1663261245550440189939487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_37
      · exact prime_sixteenN_107
      · exact prime_sixteenN_22421449
      · exact prime_sixteenN_3122914114891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1663261245550440189939487) ^ 831630622775220094969743 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663261245550440189939487) ^ 554420415183480063313162 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663261245550440189939487) ^ 44953006636498383511878 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663261245550440189939487) ^ 15544497621966730747098 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663261245550440189939487) ^ 74181701885120814 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663261245550440189939487) ^ 532599099546 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_2321014741796951690819851 : Nat.Prime 2321014741796951690819851 := by
  apply lucas_primality 2321014741796951690819851 (10 : ZMod 2321014741796951690819851)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod) = 2321014741796951690819851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_863
      · exact prime_sixteenN_935451277
      · exact prime_sixteenN_2129669261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2321014741796951690819851) ^ 1160507370898475845409925 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 773671580598983896939950 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 464202948359390338163970 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 2689472470216630000950 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 2481171172528050 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 1089847510268850 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_3001629664494629685842873 : Nat.Prime 3001629664494629685842873 := by
  apply lucas_primality 3001629664494629685842873 (3 : ZMod 3001629664494629685842873)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod) = 3001629664494629685842873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_17
      · exact prime_sixteenN_224359867
      · exact prime_sixteenN_98372345516581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3001629664494629685842873) ^ 1500814832247314842921436 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 176566450852625275637816 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 13378638990255016 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 30512941912 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_38922366554825424444818489 : Nat.Prime 38922366554825424444818489 := by
  apply lucas_primality 38922366554825424444818489 (3 : ZMod 38922366554825424444818489)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod) = 38922366554825424444818489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_234103828649
      · exact prime_sixteenN_20782640965039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38922366554825424444818489) ^ 19461183277412712222409244 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 38922366554825424444818489) ^ 166261127720312 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (3 : ZMod 38922366554825424444818489) ^ 1872830629192 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_214957615291422230456611201 : Nat.Prime 214957615291422230456611201 := by
  apply lucas_primality 214957615291422230456611201 (11 : ZMod 214957615291422230456611201)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 214957615291422230456611201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 214957615291422230456611201) ^ 107478807645711115228305600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 71652538430474076818870400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 42991523058284446091322240 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 30708230755917461493801600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 16535201176263248496662400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 12644565605377778262153600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 11313558699548538445084800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 9345983273540096976374400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 7412331561773180360572800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 6934116622303942917955200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5809665278146546769097600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5242868665644444645283200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4999014309102842568758400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4573566282796217669289600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4055804062102306235030400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3643349411719020855196800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3523895332646266073059200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_245665846047339691950412801 : Nat.Prime 245665846047339691950412801 := by
  apply lucas_primality 245665846047339691950412801 (11 : ZMod 245665846047339691950412801)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 3), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 3), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 245665846047339691950412801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 245665846047339691950412801) ^ 122832923023669845975206400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 81888615349113230650137600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 49133169209467938390082560 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 35095120863905670278630400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 18897372772872283996185600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 14450932120431746585318400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 12929781370912615365811200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 10681123741188682258713600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 8471236070597920412083200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 7924704711204506191948800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 6639617460738910593254400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 5991849903593651023180800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 5713159210403248650009600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 5226932894624248764902400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 4635204642402635697177600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 4163827899107452405939200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (11 : ZMod 245665846047339691950412801) ^ 4027308951595732654924800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_450387384420122768575756801 : Nat.Prime 450387384420122768575756801 := by
  apply lucas_primality 450387384420122768575756801 (101 : ZMod 450387384420122768575756801)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 450387384420122768575756801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 450387384420122768575756801) ^ 225193692210061384287878400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 150129128140040922858585600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 90077476884024553715151360 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 64341054917160395510822400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 40944307674556615325068800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 34645183416932520659673600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 26493375554124868739750400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 23704599180006461503987200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 19582060192179250807641600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 15530599462762854088819200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 14528625303874928018572800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 12172632011354669420966400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10985058156588360209164800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10474125219072622525017600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 9582710306811122735654400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 8497875177738165444825600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7633684481696996077555200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7383399744592176534028800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_485032567837055289235430401 : Nat.Prime 485032567837055289235430401 := by
  apply lucas_primality 485032567837055289235430401 (67 : ZMod 485032567837055289235430401)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 485032567837055289235430401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 485032567837055289235430401) ^ 242516283918527644617715200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 161677522612351763078476800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 97006513567411057847086080 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 69290366833865041319347200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 44093869803368662657766400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 28531327519826781719731200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 25528029886160804696601600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 21088372514654577792844800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 16725260959898458249497600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 15646211865711460943078400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 13108988319920413222579200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 11830062630172080225254400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 11279827159001285796172800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 10319841868873516792243200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 9151557883718024325196800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 8220890980289072698905600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 7951353571099267036646400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_652285177436039871730406401 : Nat.Prime 652285177436039871730406401 := by
  apply lucas_primality 652285177436039871730406401 (87 : ZMod 652285177436039871730406401)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 652285177436039871730406401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (87 : ZMod 652285177436039871730406401) ^ 326142588718019935865203200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 217428392478679957243468800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 130457035487207974346081280 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 93183596776577124532915200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 59298652494185442884582400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 50175782879695374748492800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 38369716319767051278259200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 34330798812423151143705600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 28360225105914777031756800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 21041457336646447475174400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 17629329119892969506227200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15909394571610728578790400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15169422731070694691404800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 13878408030554039824051200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 12307267498793205126988800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 11055680973492201215769600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 10693199630099014290662400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_5
      · exact prime_sixteenN_7
      · exact prime_sixteenN_11
      · exact prime_sixteenN_13
      · exact prime_sixteenN_17
      · exact prime_sixteenN_19
      · exact prime_sixteenN_23
      · exact prime_sixteenN_29
      · exact prime_sixteenN_31
      · exact prime_sixteenN_37
      · exact prime_sixteenN_41
      · exact prime_sixteenN_43
      · exact prime_sixteenN_47
      · exact prime_sixteenN_53
      · exact prime_sixteenN_59
      · exact prime_sixteenN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem prime_sixteenN_18916270145645156280181785697 : Nat.Prime 18916270145645156280181785697 := by
  apply lucas_primality 18916270145645156280181785697 (5 : ZMod 18916270145645156280181785697)
  · rw [← sixteenNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixteenN_2
      · exact prime_sixteenN_3
      · exact prime_sixteenN_409
      · exact prime_sixteenN_45127
      · exact prime_sixteenN_10675900157669865007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18916270145645156280181785697) ^ 9458135072822578140090892848 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 18916270145645156280181785697) ^ 6305423381881718760060595232 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 18916270145645156280181785697) ^ 46250049255856127824405344 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 18916270145645156280181785697) ^ 419178543790749579634848 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide
    · change (5 : ZMod 18916270145645156280181785697) ^ 1771866528 ≠ 1
      rw [← sixteenNFastPow_eq_pow]
      decide

private theorem phi_sixteenN_18916270145645156280181785600 : Nat.totient 18916270145645156280181785600 = 2489141895349770230169600000 := by
  rw [← show ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_7, prime_sixteenN_11, prime_sixteenN_13, prime_sixteenN_17, prime_sixteenN_19, prime_sixteenN_23, prime_sixteenN_29, prime_sixteenN_31, prime_sixteenN_37, prime_sixteenN_41, prime_sixteenN_43, prime_sixteenN_47, prime_sixteenN_53, prime_sixteenN_59, prime_sixteenN_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785601 : Nat.totient 18916270145645156280181785601 = 18916270144934553749179141204 := by
  rw [← show ((([(26620044299, 1), (710602504382600099, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_26620044299, prime_sixteenN_710602504382600099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785602 : Nat.totient 18916270145645156280181785602 = 9397888661980578118038196608 := by
  rw [← show ((([(2, 1), (157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_157, prime_sixteenN_4315799, prime_sixteenN_7041049, prime_sixteenN_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785603 : Nat.totient 18916270145645156280181785603 = 12526140360939021221625098240 := by
  rw [← show ((([(3, 1), (149, 1), (180497, 1), (27902741, 1), (8402550447737, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_149, prime_sixteenN_180497, prime_sixteenN_27902741, prime_sixteenN_8402550447737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785604 : Nat.totient 18916270145645156280181785604 = 9433519265891016348115968000 := by
  rw [← show ((([(2, 2), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_401, prime_sixteenN_11069, prime_sixteenN_53269, prime_sixteenN_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785605 : Nat.totient 18916270145645156280181785605 = 14898170181344162306248359936 := by
  rw [← show ((([(5, 1), (67, 1), (1889, 1), (13693, 1), (39926713, 1), (54675980063, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_67, prime_sixteenN_1889, prime_sixteenN_13693, prime_sixteenN_39926713, prime_sixteenN_54675980063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785606 : Nat.totient 18916270145645156280181785606 = 6292887748497342370661753184 := by
  rw [← show ((([(2, 1), (3, 1), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_503, prime_sixteenN_15040590709, prime_sixteenN_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785607 : Nat.totient 18916270145645156280181785607 = 16208314041333824177352192024 := by
  rw [← show ((([(7, 1), (2879, 1), (938632965099248562505919, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_7, prime_sixteenN_2879, prime_sixteenN_938632965099248562505919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785608 : Nat.totient 18916270145645156280181785608 = 9458090075438874484030430208 := by
  rw [← show ((([(2, 3), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_210193, prime_sixteenN_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785609 : Nat.totient 18916270145645156280181785609 = 12329361044144473180043243520 := by
  rw [← show ((([(3, 2), (83, 1), (97, 1), (13309, 1), (68891, 1), (284731330549429, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_83, prime_sixteenN_97, prime_sixteenN_13309, prime_sixteenN_68891, prime_sixteenN_284731330549429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785610 : Nat.totient 18916270145645156280181785610 = 7566418412949891821679408960 := by
  rw [← show ((([(2, 1), (5, 1), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_85243, prime_sixteenN_18480383, prime_sixteenN_23255671, prime_sixteenN_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785611 : Nat.totient 18916270145645156280181785611 = 17196609223312363224373777920 := by
  rw [← show ((([(11, 1), (13424731660273, 1), (128096483851537, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_11, prime_sixteenN_13424731660273, prime_sixteenN_128096483851537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785612 : Nat.totient 18916270145645156280181785612 = 6305423381881718760060595200 := by
  rw [← show ((([(2, 2), (3, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785613 : Nat.totient 18916270145645156280181785613 = 17458813237250731638273062976 := by
  rw [← show ((([(13, 1), (14347, 1), (15287, 1), (6634509058759861109, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_13, prime_sixteenN_14347, prime_sixteenN_15287, prime_sixteenN_6634509058759861109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785614 : Nat.totient 18916270145645156280181785614 = 8004353009181117700935702528 := by
  rw [← show ((([(2, 1), (7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_7, prime_sixteenN_79, prime_sixteenN_1272241326337, prime_sixteenN_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785615 : Nat.totient 18916270145645156280181785615 = 10088677180083373309633644576 := by
  rw [← show ((([(3, 1), (5, 1), (43687663, 1), (28865922088264225807, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_43687663, prime_sixteenN_28865922088264225807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785616 : Nat.totient 18916270145645156280181785616 = 9364438622826365116007809536 := by
  rw [← show ((([(2, 4), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_103, prime_sixteenN_5009, prime_sixteenN_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785617 : Nat.totient 18916270145645156280181785617 = 17795464654558001598715465728 := by
  rw [← show ((([(17, 1), (2287, 1), (59513, 1), (930659839, 1), (8784511289, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_17, prime_sixteenN_2287, prime_sixteenN_59513, prime_sixteenN_930659839, prime_sixteenN_8784511289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785618 : Nat.totient 18916270145645156280181785618 = 6265253988266276981853813888 := by
  rw [← show ((([(2, 1), (3, 2), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_227, prime_sixteenN_509, prime_sixteenN_106363, prime_sixteenN_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785619 : Nat.totient 18916270145645156280181785619 = 17909566826827409976127650336 := by
  rw [← show ((([(19, 1), (1613, 1), (132501777739, 1), (4658282623343, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_19, prime_sixteenN_1613, prime_sixteenN_132501777739, prime_sixteenN_4658282623343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785620 : Nat.totient 18916270145645156280181785620 = 7488393379571239139119808000 := by
  rw [← show ((([(2, 2), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_107, prime_sixteenN_1013, prime_sixteenN_144417341, prime_sixteenN_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785621 : Nat.totient 18916270145645156280181785621 = 10598942061869088945441177600 := by
  rw [← show ((([(3, 1), (7, 1), (71, 2), (353, 1), (389, 1), (17573, 1), (74050722409721, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_7, prime_sixteenN_71, prime_sixteenN_353, prime_sixteenN_389, prime_sixteenN_17573, prime_sixteenN_74050722409721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785622 : Nat.totient 18916270145645156280181785622 = 8598203787169303446000107520 := by
  rw [← show ((([(2, 1), (11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_11, prime_sixteenN_85313, prime_sixteenN_219959393, prime_sixteenN_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785623 : Nat.totient 18916270145645156280181785623 = 18093823616003981996311748224 := by
  rw [← show ((([(23, 1), (11527331273, 1), (71347522561263737, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_23, prime_sixteenN_11527331273, prime_sixteenN_71347522561263737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785624 : Nat.totient 18916270145645156280181785624 = 6286198917043595648577024000 := by
  rw [← show ((([(2, 3), (3, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_421, prime_sixteenN_1483, prime_sixteenN_2072201, prime_sixteenN_2567179, prime_sixteenN_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785625 : Nat.totient 18916270145645156280181785625 = 15132730785706553209324272000 := by
  rw [← show ((([(5, 4), (55897, 1), (1036459, 1), (522414067849459, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_55897, prime_sixteenN_1036459, prime_sixteenN_522414067849459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785626 : Nat.totient 18916270145645156280181785626 = 8697820469346636113771688960 := by
  rw [← show ((([(2, 1), (13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_13, prime_sixteenN_307, prime_sixteenN_2011, prime_sixteenN_100888969, prime_sixteenN_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785627 : Nat.totient 18916270145645156280181785627 = 12610843282295425563125778144 := by
  rw [← show ((([(3, 3), (3972037, 1), (41136839, 1), (4287731098507, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_3972037, prime_sixteenN_41136839, prime_sixteenN_4287731098507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785628 : Nat.totient 18916270145645156280181785628 = 8099514802800883054387193904 := by
  rw [← show ((([(2, 2), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_7, prime_sixteenN_1087, prime_sixteenN_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785629 : Nat.totient 18916270145645156280181785629 = 18263984968209116408451379200 := by
  rw [← show ((([(29, 1), (652285177436039871730406401, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_29, prime_sixteenN_652285177436039871730406401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785630 : Nat.totient 18916270145645156280181785630 = 5044262926251492700075547904 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_66569, prime_sixteenN_1596046247, prime_sixteenN_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785631 : Nat.totient 18916270145645156280181785631 = 18281076342659919067790352000 := by
  rw [← show ((([(31, 1), (839, 1), (6197, 1), (82301, 1), (1426018778793047, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_31, prime_sixteenN_839, prime_sixteenN_6197, prime_sixteenN_82301, prime_sixteenN_1426018778793047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785632 : Nat.totient 18916270145645156280181785632 = 9458135065086595926115297600 := by
  rw [← show ((([(2, 5), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_1222615931, prime_sixteenN_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785633 : Nat.totient 18916270145645156280181785633 = 11461129667245573256539224000 := by
  rw [← show ((([(3, 1), (11, 1), (3499, 1), (13053027349, 1), (12550654586551, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_11, prime_sixteenN_3499, prime_sixteenN_13053027349, prime_sixteenN_12550654586551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785634 : Nat.totient 18916270145645156280181785634 = 8889066415381478401011130368 := by
  rw [← show ((([(2, 1), (17, 1), (709, 1), (58337, 1), (13451362101445396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_17, prime_sixteenN_709, prime_sixteenN_58337, prime_sixteenN_13451362101445396397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785635 : Nat.totient 18916270145645156280181785635 = 12971156671261848722052784128 := by
  rw [← show ((([(5, 1), (7, 1), (344256547937, 1), (1569947948827553, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_7, prime_sixteenN_344256547937, prime_sixteenN_1569947948827553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785636 : Nat.totient 18916270145645156280181785636 = 6305423381881718760060595200 := by
  rw [← show ((([(2, 2), (3, 2), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785637 : Nat.totient 18916270145645156280181785637 = 18403967344601959309194152400 := by
  rw [← show ((([(37, 1), (17491, 1), (29229349063912647400411, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_37, prime_sixteenN_17491, prime_sixteenN_29229349063912647400411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785638 : Nat.totient 18916270145645156280181785638 = 8960338490019463528833605472 := by
  rw [← show ((([(2, 1), (19, 1), (390056504429, 1), (1276216592026469, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_19, prime_sixteenN_390056504429, prime_sixteenN_1276216592026469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785639 : Nat.totient 18916270145645156280181785639 = 11640781628089326941650329600 := by
  rw [← show ((([(3, 1), (13, 1), (485032567837055289235430401, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_13, prime_sixteenN_485032567837055289235430401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785640 : Nat.totient 18916270145645156280181785640 = 7533101469501398473590152448 := by
  rw [← show ((([(2, 3), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_239, prime_sixteenN_4327, prime_sixteenN_1214459, prime_sixteenN_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785641 : Nat.totient 18916270145645156280181785641 = 18441876672636518188932249600 := by
  rw [← show ((([(41, 1), (1693, 1), (8699, 1), (232001521, 1), (135031325183, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_41, prime_sixteenN_1693, prime_sixteenN_8699, prime_sixteenN_232001521, prime_sixteenN_135031325183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785642 : Nat.totient 18916270145645156280181785642 = 5404648613041473222909081600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (450387384420122768575756801, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_7, prime_sixteenN_450387384420122768575756801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785643 : Nat.totient 18916270145645156280181785643 = 18452873579810226421194570240 := by
  rw [← show ((([(43, 1), (881, 1), (7349, 1), (67945843775149768429, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_43, prime_sixteenN_881, prime_sixteenN_7349, prime_sixteenN_67945843775149768429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785644 : Nat.totient 18916270145645156280181785644 = 8596761758684795040349213440 := by
  rw [← show ((([(2, 2), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_11, prime_sixteenN_5573, prime_sixteenN_3198253273, prime_sixteenN_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785645 : Nat.totient 18916270145645156280181785645 = 9978683977832279813087846400 := by
  rw [← show ((([(3, 2), (5, 1), (113, 1), (499, 1), (24971, 1), (36341, 1), (8215068638333, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_113, prime_sixteenN_499, prime_sixteenN_24971, prime_sixteenN_36341, prime_sixteenN_8215068638333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785646 : Nat.totient 18916270145645156280181785646 = 8980875956167932020041873024 := by
  rw [← show ((([(2, 1), (23, 1), (137, 1), (3001629664494629685842873, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_23, prime_sixteenN_137, prime_sixteenN_3001629664494629685842873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785647 : Nat.totient 18916270145645156280181785647 = 18513796305495720767450539032 := by
  rw [← show ((([(47, 1), (2548927123, 1), (157899309577893787, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_47, prime_sixteenN_2548927123, prime_sixteenN_157899309577893787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785648 : Nat.totient 18916270145645156280181785648 = 6305423381881718760060595200 := by
  rw [← show ((([(2, 4), (3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785649 : Nat.totient 18916270145645156280181785649 = 16122835775759527267577832960 := by
  rw [← show ((([(7, 4), (179, 1), (30557, 1), (9420721, 1), (152895766423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_7, prime_sixteenN_179, prime_sixteenN_30557, prime_sixteenN_9420721, prime_sixteenN_152895766423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785650 : Nat.totient 18916270145645156280181785650 = 7520087763422123478256314000 := by
  rw [← show ((([(2, 1), (5, 2), (163, 1), (2321014741796951690819851, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_163, prime_sixteenN_2321014741796951690819851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785651 : Nat.totient 18916270145645156280181785651 = 11815807888390327109330108544 := by
  rw [← show ((([(3, 1), (17, 1), (223, 1), (1663261245550440189939487, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_17, prime_sixteenN_223, prime_sixteenN_1663261245550440189939487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785652 : Nat.totient 18916270145645156280181785652 = 8695803009030871719360300000 := by
  rw [← show ((([(2, 2), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_13, prime_sixteenN_251, prime_sixteenN_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785653 : Nat.totient 18916270145645156280181785653 = 18559357995543725111319859200 := by
  rw [← show ((([(53, 1), (13509889, 1), (1022142959, 1), (25846171151, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_53, prime_sixteenN_13509889, prime_sixteenN_1022142959, prime_sixteenN_25846171151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785654 : Nat.totient 18916270145645156280181785654 = 6305423381881718760060595056 := by
  rw [← show ((([(2, 1), (3, 5), (38922366554825424444818489, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_38922366554825424444818489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785655 : Nat.totient 18916270145645156280181785655 = 13756237118466667116366977280 := by
  rw [← show ((([(5, 1), (11, 1), (13099, 1), (2546581993, 1), (10310435557003, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_11, prime_sixteenN_13099, prime_sixteenN_2546581993, prime_sixteenN_10310435557003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785656 : Nat.totient 18916270145645156280181785656 = 8106889790731887118593367008 := by
  rw [← show ((([(2, 3), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_7, prime_sixteenN_97523, prime_sixteenN_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785657 : Nat.totient 18916270145645156280181785657 = 11933945486902156795516087488 := by
  rw [← show ((([(3, 1), (19, 1), (907, 1), (31896439, 1), (11471261097382837, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_19, prime_sixteenN_907, prime_sixteenN_31896439, prime_sixteenN_11471261097382837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785658 : Nat.totient 18916270145645156280181785658 = 9131530408889049194550277936 := by
  rw [← show ((([(2, 1), (29, 1), (19763, 1), (16502686268178916959227, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_29, prime_sixteenN_19763, prime_sixteenN_16502686268178916959227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785659 : Nat.totient 18916270145645156280181785659 = 18411539997391125294491829600 := by
  rw [← show ((([(59, 1), (101, 1), (399877183627, 1), (7938446047463, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_59, prime_sixteenN_101, prime_sixteenN_399877183627, prime_sixteenN_7938446047463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785660 : Nat.totient 18916270145645156280181785660 = 5044045106359756367392093440 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (22397, 1), (73771, 1), (190813341386997503, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_22397, prime_sixteenN_73771, prime_sixteenN_190813341386997503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785661 : Nat.totient 18916270145645156280181785661 = 18498617255998983919987653120 := by
  rw [← show ((([(61, 1), (173, 1), (430089759833, 1), (4167738550189, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_61, prime_sixteenN_173, prime_sixteenN_430089759833, prime_sixteenN_4167738550189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785662 : Nat.totient 18916270145645156280181785662 = 9135938550966438558512954880 := by
  rw [← show ((([(2, 1), (31, 1), (547, 1), (25307, 1), (7487737, 1), (2943508165337, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_31, prime_sixteenN_547, prime_sixteenN_25307, prime_sixteenN_7487737, prime_sixteenN_2943508165337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785663 : Nat.totient 18916270145645156280181785663 = 10809295779615842356147967040 := by
  rw [← show ((([(3, 2), (7, 1), (7682093, 1), (274948067, 1), (142155846871, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_7, prime_sixteenN_7682093, prime_sixteenN_274948067, prime_sixteenN_142155846871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785664 : Nat.totient 18916270145645156280181785664 = 9458134620944793194601529344 := by
  rw [← show ((([(2, 6), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_20930737, prime_sixteenN_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785665 : Nat.totient 18916270145645156280181785665 = 13950738015690132158320465920 := by
  rw [← show ((([(5, 1), (13, 1), (773, 1), (108271, 1), (1409138009, 1), (2467612603, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_13, prime_sixteenN_773, prime_sixteenN_108271, prime_sixteenN_1409138009, prime_sixteenN_2467612603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785666 : Nat.totient 18916270145645156280181785666 = 5731495482304186652590848000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (8101, 1), (64859654689, 1), (545479341709, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_11, prime_sixteenN_8101, prime_sixteenN_64859654689, prime_sixteenN_545479341709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785667 : Nat.totient 18916270145645156280181785667 = 18916269977094169068018947520 := by
  rw [← show ((([(112228771, 1), (168550987212050609377, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_112228771, prime_sixteenN_168550987212050609377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785668 : Nat.totient 18916270145645156280181785668 = 8774069760182884202690641920 := by
  rw [← show ((([(2, 2), (17, 1), (73, 1), (1609, 1), (29021, 1), (2685877, 1), (30384297329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_17, prime_sixteenN_73, prime_sixteenN_1609, prime_sixteenN_29021, prime_sixteenN_2685877, prime_sixteenN_30384297329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785669 : Nat.totient 18916270145645156280181785669 = 12062549052100145410684747776 := by
  rw [← show ((([(3, 1), (23, 1), (458961409, 1), (597324387877913089, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_23, prime_sixteenN_458961409, prime_sixteenN_597324387877913089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785670 : Nat.totient 18916270145645156280181785670 = 6485424168252302859488640000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (54287, 1), (193451, 1), (5530901, 1), (4652375513, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_7, prime_sixteenN_54287, prime_sixteenN_193451, prime_sixteenN_5530901, prime_sixteenN_4652375513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785671 : Nat.totient 18916270145645156280181785671 = 18894943431707673946782770200 := by
  rw [← show ((([(887, 1), (31916351, 1), (668187974337575183, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_887, prime_sixteenN_31916351, prime_sixteenN_668187974337575183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785672 : Nat.totient 18916270145645156280181785672 = 6192819318588176905531084800 := by
  rw [← show ((([(2, 3), (3, 2), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_67, prime_sixteenN_491, prime_sixteenN_1061, prime_sixteenN_9492089, prime_sixteenN_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785673 : Nat.totient 18916270145645156280181785673 = 18884950920361190659827605136 := by
  rw [← show ((([(827, 1), (2237, 1), (10225016416573823164327, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_827, prime_sixteenN_2237, prime_sixteenN_10225016416573823164327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785674 : Nat.totient 18916270145645156280181785674 = 9202503571738770533393366208 := by
  rw [← show ((([(2, 1), (37, 1), (2351599, 1), (3974227, 1), (27351922138837, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_37, prime_sixteenN_2351599, prime_sixteenN_3974227, prime_sixteenN_27351922138837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785675 : Nat.totient 18916270145645156280181785675 = 9973423883379826422910156800 := by
  rw [← show ((([(3, 1), (5, 2), (89, 1), (5881, 1), (65927, 1), (198977, 1), (36733885319, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_89, prime_sixteenN_5881, prime_sixteenN_65927, prime_sixteenN_198977, prime_sixteenN_36733885319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785676 : Nat.totient 18916270145645156280181785676 = 8940935309538484637810675712 := by
  rw [← show ((([(2, 2), (19, 1), (463, 1), (177409, 1), (3030158014634483503, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_19, prime_sixteenN_463, prime_sixteenN_177409, prime_sixteenN_3030158014634483503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785677 : Nat.totient 18916270145645156280181785677 = 14739950762840381517024768000 := by
  rw [← show ((([(7, 1), (11, 1), (245665846047339691950412801, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_7, prime_sixteenN_11, prime_sixteenN_245665846047339691950412801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785678 : Nat.totient 18916270145645156280181785678 = 5798753673472006729297850112 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (269, 1), (69349809527745966433433, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_13, prime_sixteenN_269, prime_sixteenN_69349809527745966433433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785679 : Nat.totient 18916270145645156280181785679 = 18916262159547538453551206400 := by
  rw [← show ((([(4451401, 1), (11731007, 1), (13169249, 1), (27506953, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_4451401, prime_sixteenN_11731007, prime_sixteenN_13169249, prime_sixteenN_27506953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785680 : Nat.totient 18916270145645156280181785680 = 7566508046172546654591348864 := by
  rw [← show ((([(2, 4), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_5, prime_sixteenN_626080687, prime_sixteenN_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785681 : Nat.totient 18916270145645156280181785681 = 12607595182545726715329640320 := by
  rw [← show ((([(3, 3), (3881, 1), (5729557, 1), (31507000248526559, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_3881, prime_sixteenN_5729557, prime_sixteenN_31507000248526559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785682 : Nat.totient 18916270145645156280181785682 = 9118910388684245109645888000 := by
  rw [← show ((([(2, 1), (41, 1), (109, 1), (383, 1), (834859, 1), (18321287, 1), (361266151, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_41, prime_sixteenN_109, prime_sixteenN_383, prime_sixteenN_834859, prime_sixteenN_18321287, prime_sixteenN_361266151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785683 : Nat.totient 18916270145645156280181785683 = 18859262257535046449111323776 := by
  rw [← show ((([(337, 1), (21517, 1), (2608698490372481172527, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_337, prime_sixteenN_21517, prime_sixteenN_2608698490372481172527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785684 : Nat.totient 18916270145645156280181785684 = 5404648613024653378691212896 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (321473185079, 1), (700505369226119, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_7, prime_sixteenN_321473185079, prime_sixteenN_700505369226119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785685 : Nat.totient 18916270145645156280181785685 = 14242838697873457162168366336 := by
  rw [← show ((([(5, 1), (17, 1), (592603554899, 1), (375536651467739, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_17, prime_sixteenN_592603554899, prime_sixteenN_375536651467739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785686 : Nat.totient 18916270145645156280181785686 = 9224197704901156185626473440 := by
  rw [← show ((([(2, 1), (43, 1), (661, 1), (1973467, 1), (168618696733348423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_43, prime_sixteenN_661, prime_sixteenN_1973467, prime_sixteenN_168618696733348423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785687 : Nat.totient 18916270145645156280181785687 = 12056467990971720650232729600 := by
  rw [← show ((([(3, 1), (29, 1), (151, 1), (397, 1), (1433, 1), (144778493, 1), (17482299607, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_29, prime_sixteenN_151, prime_sixteenN_397, prime_sixteenN_1433, prime_sixteenN_144778493, prime_sixteenN_17482299607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785688 : Nat.totient 18916270145645156280181785688 = 8598304611656889218264448000 := by
  rw [← show ((([(2, 3), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_11, prime_sixteenN_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785689 : Nat.totient 18916270145645156280181785689 = 18916270145602332493298646756 := by
  rw [← show ((([(441727989187, 1), (42823345155149747, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_441727989187, prime_sixteenN_42823345155149747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785690 : Nat.totient 18916270145645156280181785690 = 5041350646922954404494574848 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (2803, 1), (4243, 1), (17672454355456607929, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_5, prime_sixteenN_2803, prime_sixteenN_4243, prime_sixteenN_17672454355456607929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785691 : Nat.totient 18916270145645156280181785691 = 14966719235254236540602671488 := by
  rw [← show ((([(7, 1), (13, 1), (17390803669, 1), (11952932392200829, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_7, prime_sixteenN_13, prime_sixteenN_17390803669, prime_sixteenN_11952932392200829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785692 : Nat.totient 18916270145645156280181785692 = 8812026774552233434883271360 := by
  rw [← show ((([(2, 2), (23, 1), (71, 1), (83, 1), (34890825049700005681357, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_23, prime_sixteenN_71, prime_sixteenN_83, prime_sixteenN_34890825049700005681357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785693 : Nat.totient 18916270145645156280181785693 = 12048447411561147685080353280 := by
  rw [← show ((([(3, 1), (31, 1), (79, 1), (13049, 1), (62477, 1), (3158115935550403, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_3, prime_sixteenN_31, prime_sixteenN_79, prime_sixteenN_13049, prime_sixteenN_62477, prime_sixteenN_3158115935550403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785694 : Nat.totient 18916270145645156280181785694 = 9217024555176450862370287360 := by
  rw [← show ((([(2, 1), (47, 1), (233, 1), (64439, 1), (6643181, 1), (2017561841483, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_47, prime_sixteenN_233, prime_sixteenN_64439, prime_sixteenN_6643181, prime_sixteenN_2017561841483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785695 : Nat.totient 18916270145645156280181785695 = 14230247128687225980859576320 := by
  rw [← show ((([(5, 1), (19, 1), (139, 1), (4513, 1), (15274007543, 1), (20781589781, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_5, prime_sixteenN_19, prime_sixteenN_139, prime_sixteenN_4513, prime_sixteenN_15274007543, prime_sixteenN_20781589781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785696 : Nat.totient 18916270145645156280181785696 = 6289867314243974845772430336 := by
  rw [← show ((([(2, 5), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_3, prime_sixteenN_409, prime_sixteenN_45127, prime_sixteenN_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785697 : Nat.totient 18916270145645156280181785697 = 18916270145645156280181785696 := by
  rw [← show ((([(18916270145645156280181785697, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_18916270145645156280181785697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixteenN_18916270145645156280181785698 : Nat.totient 18916270145645156280181785698 = 8106179153979338060134746240 := by
  rw [← show ((([(2, 1), (7, 2), (10739, 1), (212573, 1), (11239603, 1), (7522921261, 1)] : List FactorBlock).map factorBlockValue).prod) = 18916270145645156280181785698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixteenN_2, prime_sixteenN_7, prime_sixteenN_10739, prime_sixteenN_212573, prime_sixteenN_11239603, prime_sixteenN_7522921261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixteenN : certifiedKill 1 18916270145645156280181785599 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixteenN_18916270145645156280181785600, phi_sixteenN_18916270145645156280181785601, phi_sixteenN_18916270145645156280181785602,
    phi_sixteenN_18916270145645156280181785603, phi_sixteenN_18916270145645156280181785604, phi_sixteenN_18916270145645156280181785605,
    phi_sixteenN_18916270145645156280181785606, phi_sixteenN_18916270145645156280181785607, phi_sixteenN_18916270145645156280181785608,
    phi_sixteenN_18916270145645156280181785609, phi_sixteenN_18916270145645156280181785610, phi_sixteenN_18916270145645156280181785611,
    phi_sixteenN_18916270145645156280181785612, phi_sixteenN_18916270145645156280181785613, phi_sixteenN_18916270145645156280181785614,
    phi_sixteenN_18916270145645156280181785615, phi_sixteenN_18916270145645156280181785616, phi_sixteenN_18916270145645156280181785617,
    phi_sixteenN_18916270145645156280181785618, phi_sixteenN_18916270145645156280181785619, phi_sixteenN_18916270145645156280181785620,
    phi_sixteenN_18916270145645156280181785621, phi_sixteenN_18916270145645156280181785622, phi_sixteenN_18916270145645156280181785623,
    phi_sixteenN_18916270145645156280181785624, phi_sixteenN_18916270145645156280181785625, phi_sixteenN_18916270145645156280181785626,
    phi_sixteenN_18916270145645156280181785627, phi_sixteenN_18916270145645156280181785628, phi_sixteenN_18916270145645156280181785629,
    phi_sixteenN_18916270145645156280181785630, phi_sixteenN_18916270145645156280181785631, phi_sixteenN_18916270145645156280181785632,
    phi_sixteenN_18916270145645156280181785633, phi_sixteenN_18916270145645156280181785634, phi_sixteenN_18916270145645156280181785635,
    phi_sixteenN_18916270145645156280181785636, phi_sixteenN_18916270145645156280181785637, phi_sixteenN_18916270145645156280181785638,
    phi_sixteenN_18916270145645156280181785639, phi_sixteenN_18916270145645156280181785640, phi_sixteenN_18916270145645156280181785641,
    phi_sixteenN_18916270145645156280181785642, phi_sixteenN_18916270145645156280181785643, phi_sixteenN_18916270145645156280181785644,
    phi_sixteenN_18916270145645156280181785645, phi_sixteenN_18916270145645156280181785646, phi_sixteenN_18916270145645156280181785647,
    phi_sixteenN_18916270145645156280181785648, phi_sixteenN_18916270145645156280181785649, phi_sixteenN_18916270145645156280181785650,
    phi_sixteenN_18916270145645156280181785651, phi_sixteenN_18916270145645156280181785652, phi_sixteenN_18916270145645156280181785653,
    phi_sixteenN_18916270145645156280181785654, phi_sixteenN_18916270145645156280181785655, phi_sixteenN_18916270145645156280181785656,
    phi_sixteenN_18916270145645156280181785657, phi_sixteenN_18916270145645156280181785658, phi_sixteenN_18916270145645156280181785659,
    phi_sixteenN_18916270145645156280181785660, phi_sixteenN_18916270145645156280181785661, phi_sixteenN_18916270145645156280181785662,
    phi_sixteenN_18916270145645156280181785663, phi_sixteenN_18916270145645156280181785664, phi_sixteenN_18916270145645156280181785665,
    phi_sixteenN_18916270145645156280181785666, phi_sixteenN_18916270145645156280181785667, phi_sixteenN_18916270145645156280181785668,
    phi_sixteenN_18916270145645156280181785669, phi_sixteenN_18916270145645156280181785670, phi_sixteenN_18916270145645156280181785671,
    phi_sixteenN_18916270145645156280181785672, phi_sixteenN_18916270145645156280181785673, phi_sixteenN_18916270145645156280181785674,
    phi_sixteenN_18916270145645156280181785675, phi_sixteenN_18916270145645156280181785676, phi_sixteenN_18916270145645156280181785677,
    phi_sixteenN_18916270145645156280181785678, phi_sixteenN_18916270145645156280181785679, phi_sixteenN_18916270145645156280181785680,
    phi_sixteenN_18916270145645156280181785681, phi_sixteenN_18916270145645156280181785682, phi_sixteenN_18916270145645156280181785683,
    phi_sixteenN_18916270145645156280181785684, phi_sixteenN_18916270145645156280181785685, phi_sixteenN_18916270145645156280181785686,
    phi_sixteenN_18916270145645156280181785687, phi_sixteenN_18916270145645156280181785688, phi_sixteenN_18916270145645156280181785689,
    phi_sixteenN_18916270145645156280181785690, phi_sixteenN_18916270145645156280181785691, phi_sixteenN_18916270145645156280181785692,
    phi_sixteenN_18916270145645156280181785693, phi_sixteenN_18916270145645156280181785694, phi_sixteenN_18916270145645156280181785695,
    phi_sixteenN_18916270145645156280181785696, phi_sixteenN_18916270145645156280181785697, phi_sixteenN_18916270145645156280181785698]

end TotientTailPeriodKiller
end Erdos249257
