import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyALFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyALFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyALFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyALFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyALFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyALFastPow a n * fortyALFastPow a n * a
        else fortyALFastPow a n * fortyALFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyAL_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyAL_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyAL_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyAL_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyAL_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyAL_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyAL_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyAL_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyAL_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyAL_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyAL_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyAL_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyAL_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyAL_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyAL_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyAL_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyAL_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyAL_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyAL_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyAL_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyAL_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyAL_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyAL_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyAL_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyAL_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyAL_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyAL_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyAL_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyAL_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyAL_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyAL_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyAL_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyAL_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyAL_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyAL_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyAL_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyAL_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyAL_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyAL_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyAL_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyAL_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyAL_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyAL_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyAL_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortyAL_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyAL_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyAL_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyAL_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyAL_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyAL_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyAL_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyAL_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyAL_271 : Nat.Prime 271 := by norm_num
private theorem prime_fortyAL_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyAL_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyAL_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyAL_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyAL_311 : Nat.Prime 311 := by norm_num
private theorem prime_fortyAL_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyAL_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyAL_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyAL_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyAL_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyAL_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyAL_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyAL_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyAL_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortyAL_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyAL_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyAL_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyAL_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyAL_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortyAL_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortyAL_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyAL_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortyAL_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortyAL_463 : Nat.Prime 463 := by norm_num
private theorem prime_fortyAL_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortyAL_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortyAL_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyAL_503 : Nat.Prime 503 := by norm_num
private theorem prime_fortyAL_509 : Nat.Prime 509 := by norm_num
private theorem prime_fortyAL_523 : Nat.Prime 523 := by norm_num
private theorem prime_fortyAL_541 : Nat.Prime 541 := by norm_num
private theorem prime_fortyAL_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortyAL_569 : Nat.Prime 569 := by norm_num
private theorem prime_fortyAL_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortyAL_587 : Nat.Prime 587 := by norm_num
private theorem prime_fortyAL_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyAL_613 : Nat.Prime 613 := by norm_num
private theorem prime_fortyAL_617 : Nat.Prime 617 := by norm_num
private theorem prime_fortyAL_619 : Nat.Prime 619 := by norm_num
private theorem prime_fortyAL_631 : Nat.Prime 631 := by norm_num
private theorem prime_fortyAL_673 : Nat.Prime 673 := by norm_num
private theorem prime_fortyAL_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortyAL_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortyAL_719 : Nat.Prime 719 := by norm_num
private theorem prime_fortyAL_733 : Nat.Prime 733 := by norm_num
private theorem prime_fortyAL_743 : Nat.Prime 743 := by norm_num
private theorem prime_fortyAL_761 : Nat.Prime 761 := by norm_num
private theorem prime_fortyAL_809 : Nat.Prime 809 := by norm_num
private theorem prime_fortyAL_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyAL_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortyAL_829 : Nat.Prime 829 := by norm_num
private theorem prime_fortyAL_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortyAL_859 : Nat.Prime 859 := by norm_num
private theorem prime_fortyAL_881 : Nat.Prime 881 := by norm_num
private theorem prime_fortyAL_937 : Nat.Prime 937 := by norm_num
private theorem prime_fortyAL_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortyAL_977 : Nat.Prime 977 := by norm_num
private theorem prime_fortyAL_983 : Nat.Prime 983 := by norm_num
private theorem prime_fortyAL_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyAL_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fortyAL_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fortyAL_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fortyAL_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fortyAL_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fortyAL_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fortyAL_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_fortyAL_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_fortyAL_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fortyAL_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_fortyAL_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_fortyAL_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fortyAL_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fortyAL_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_fortyAL_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_fortyAL_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fortyAL_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_fortyAL_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_fortyAL_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_fortyAL_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyAL_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_fortyAL_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyAL_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_fortyAL_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_fortyAL_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fortyAL_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fortyAL_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_fortyAL_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_fortyAL_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_fortyAL_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fortyAL_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fortyAL_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_fortyAL_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fortyAL_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fortyAL_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_fortyAL_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_fortyAL_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fortyAL_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_fortyAL_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_fortyAL_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_fortyAL_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyAL_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_fortyAL_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_fortyAL_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_fortyAL_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_fortyAL_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fortyAL_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_fortyAL_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_fortyAL_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fortyAL_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_fortyAL_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_fortyAL_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_fortyAL_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_fortyAL_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_fortyAL_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_fortyAL_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_fortyAL_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_fortyAL_4057 : Nat.Prime 4057 := by norm_num
private theorem prime_fortyAL_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_fortyAL_4523 : Nat.Prime 4523 := by norm_num
private theorem prime_fortyAL_4783 : Nat.Prime 4783 := by norm_num
private theorem prime_fortyAL_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_fortyAL_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyAL_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_fortyAL_5119 : Nat.Prime 5119 := by norm_num
private theorem prime_fortyAL_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_fortyAL_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_fortyAL_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fortyAL_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fortyAL_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_fortyAL_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_fortyAL_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_fortyAL_6269 : Nat.Prime 6269 := by norm_num
private theorem prime_fortyAL_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fortyAL_6547 : Nat.Prime 6547 := by norm_num
private theorem prime_fortyAL_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_fortyAL_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyAL_7151 : Nat.Prime 7151 := by norm_num
private theorem prime_fortyAL_7433 : Nat.Prime 7433 := by norm_num
private theorem prime_fortyAL_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_fortyAL_7841 : Nat.Prime 7841 := by norm_num
private theorem prime_fortyAL_7867 : Nat.Prime 7867 := by norm_num
private theorem prime_fortyAL_8581 : Nat.Prime 8581 := by norm_num
private theorem prime_fortyAL_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_fortyAL_9221 : Nat.Prime 9221 := by norm_num
private theorem prime_fortyAL_9871 : Nat.Prime 9871 := by norm_num
private theorem prime_fortyAL_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fortyAL_10949 : Nat.Prime 10949 := by norm_num
private theorem prime_fortyAL_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_fortyAL_11443 : Nat.Prime 11443 := by norm_num
private theorem prime_fortyAL_11779 : Nat.Prime 11779 := by norm_num
private theorem prime_fortyAL_11863 : Nat.Prime 11863 := by norm_num
private theorem prime_fortyAL_12251 : Nat.Prime 12251 := by norm_num
private theorem prime_fortyAL_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_fortyAL_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_fortyAL_14401 : Nat.Prime 14401 := by norm_num
private theorem prime_fortyAL_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_fortyAL_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_fortyAL_17417 : Nat.Prime 17417 := by norm_num
private theorem prime_fortyAL_17737 : Nat.Prime 17737 := by norm_num
private theorem prime_fortyAL_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_fortyAL_18919 : Nat.Prime 18919 := by norm_num
private theorem prime_fortyAL_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_fortyAL_19073 : Nat.Prime 19073 := by norm_num
private theorem prime_fortyAL_19141 : Nat.Prime 19141 := by norm_num
private theorem prime_fortyAL_19381 : Nat.Prime 19381 := by norm_num
private theorem prime_fortyAL_20789 : Nat.Prime 20789 := by norm_num
private theorem prime_fortyAL_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_fortyAL_22973 : Nat.Prime 22973 := by norm_num
private theorem prime_fortyAL_24113 : Nat.Prime 24113 := by norm_num
private theorem prime_fortyAL_24793 : Nat.Prime 24793 := by norm_num
private theorem prime_fortyAL_25733 : Nat.Prime 25733 := by norm_num
private theorem prime_fortyAL_25867 : Nat.Prime 25867 := by norm_num
private theorem prime_fortyAL_27799 : Nat.Prime 27799 := by norm_num
private theorem prime_fortyAL_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_fortyAL_30773 : Nat.Prime 30773 := by norm_num
private theorem prime_fortyAL_30871 : Nat.Prime 30871 := by norm_num
private theorem prime_fortyAL_31859 : Nat.Prime 31859 := by norm_num
private theorem prime_fortyAL_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyAL_35573 : Nat.Prime 35573 := by norm_num
private theorem prime_fortyAL_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_fortyAL_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyAL_39607 : Nat.Prime 39607 := by norm_num
private theorem prime_fortyAL_40039 : Nat.Prime 40039 := by norm_num
private theorem prime_fortyAL_42337 : Nat.Prime 42337 := by norm_num
private theorem prime_fortyAL_44647 : Nat.Prime 44647 := by norm_num
private theorem prime_fortyAL_47797 : Nat.Prime 47797 := by norm_num
private theorem prime_fortyAL_50101 : Nat.Prime 50101 := by norm_num
private theorem prime_fortyAL_51949 : Nat.Prime 51949 := by norm_num
private theorem prime_fortyAL_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_fortyAL_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_fortyAL_56299 : Nat.Prime 56299 := by norm_num
private theorem prime_fortyAL_58337 : Nat.Prime 58337 := by norm_num
private theorem prime_fortyAL_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_fortyAL_61553 : Nat.Prime 61553 := by norm_num
private theorem prime_fortyAL_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyAL_61729 : Nat.Prime 61729 := by norm_num
private theorem prime_fortyAL_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_fortyAL_65963 : Nat.Prime 65963 := by norm_num
private theorem prime_fortyAL_66569 : Nat.Prime 66569 := by norm_num
private theorem prime_fortyAL_67261 : Nat.Prime 67261 := by norm_num
private theorem prime_fortyAL_74489 : Nat.Prime 74489 := by norm_num
private theorem prime_fortyAL_81761 : Nat.Prime 81761 := by norm_num
private theorem prime_fortyAL_85243 : Nat.Prime 85243 := by norm_num
private theorem prime_fortyAL_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_fortyAL_85313 : Nat.Prime 85313 := by norm_num
private theorem prime_fortyAL_92377 : Nat.Prime 92377 := by norm_num
private theorem prime_fortyAL_94109 : Nat.Prime 94109 := by norm_num
private theorem prime_fortyAL_97387 : Nat.Prime 97387 := by norm_num
private theorem prime_fortyAL_98507 : Nat.Prime 98507 := by norm_num
private theorem prime_fortyAL_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_fortyAL_102593 : Nat.Prime 102593 := by norm_num
private theorem prime_fortyAL_105607 : Nat.Prime 105607 := by norm_num
private theorem prime_fortyAL_106363 : Nat.Prime 106363 := by norm_num
private theorem prime_fortyAL_108631 : Nat.Prime 108631 := by norm_num
private theorem prime_fortyAL_114997 : Nat.Prime 114997 := by norm_num
private theorem prime_fortyAL_116329 : Nat.Prime 116329 := by norm_num
private theorem prime_fortyAL_117413 : Nat.Prime 117413 := by norm_num
private theorem prime_fortyAL_119069 : Nat.Prime 119069 := by norm_num
private theorem prime_fortyAL_119557 : Nat.Prime 119557 := by norm_num
private theorem prime_fortyAL_119881 : Nat.Prime 119881 := by norm_num
private theorem prime_fortyAL_123401 : Nat.Prime 123401 := by norm_num
private theorem prime_fortyAL_123433 : Nat.Prime 123433 := by norm_num
private theorem prime_fortyAL_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_fortyAL_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_fortyAL_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fortyAL_220889 : Nat.Prime 220889 := by norm_num
private theorem prime_fortyAL_225749 : Nat.Prime 225749 := by norm_num
private theorem prime_fortyAL_226901 : Nat.Prime 226901 := by norm_num
private theorem prime_fortyAL_242989 : Nat.Prime 242989 := by norm_num
private theorem prime_fortyAL_243787 : Nat.Prime 243787 := by norm_num
private theorem prime_fortyAL_263761 : Nat.Prime 263761 := by norm_num
private theorem prime_fortyAL_267373 : Nat.Prime 267373 := by norm_num
private theorem prime_fortyAL_287801 : Nat.Prime 287801 := by norm_num
private theorem prime_fortyAL_293081 : Nat.Prime 293081 := by norm_num
private theorem prime_fortyAL_304067 : Nat.Prime 304067 := by norm_num
private theorem prime_fortyAL_321721 : Nat.Prime 321721 := by norm_num
private theorem prime_fortyAL_322951 : Nat.Prime 322951 := by norm_num
private theorem prime_fortyAL_330247 : Nat.Prime 330247 := by norm_num
private theorem prime_fortyAL_345637 : Nat.Prime 345637 := by norm_num
private theorem prime_fortyAL_352409 : Nat.Prime 352409 := by norm_num
private theorem prime_fortyAL_354829 : Nat.Prime 354829 := by norm_num
private theorem prime_fortyAL_374681 : Nat.Prime 374681 := by norm_num
private theorem prime_fortyAL_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_fortyAL_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_fortyAL_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_fortyAL_396107 : Nat.Prime 396107 := by norm_num
private theorem prime_fortyAL_396971 : Nat.Prime 396971 := by norm_num
private theorem prime_fortyAL_397153 : Nat.Prime 397153 := by norm_num
private theorem prime_fortyAL_410497 : Nat.Prime 410497 := by norm_num
private theorem prime_fortyAL_415799 : Nat.Prime 415799 := by norm_num
private theorem prime_fortyAL_458929 : Nat.Prime 458929 := by norm_num
private theorem prime_fortyAL_463291 : Nat.Prime 463291 := by norm_num
private theorem prime_fortyAL_501037 : Nat.Prime 501037 := by norm_num
private theorem prime_fortyAL_505097 : Nat.Prime 505097 := by norm_num
private theorem prime_fortyAL_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_fortyAL_595201 : Nat.Prime 595201 := by norm_num
private theorem prime_fortyAL_596369 : Nat.Prime 596369 := by norm_num
private theorem prime_fortyAL_644549 : Nat.Prime 644549 := by norm_num
private theorem prime_fortyAL_655559 : Nat.Prime 655559 := by norm_num
private theorem prime_fortyAL_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_fortyAL_674701 : Nat.Prime 674701 := by norm_num
private theorem prime_fortyAL_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_fortyAL_777979 : Nat.Prime 777979 := by norm_num
private theorem prime_fortyAL_798923 : Nat.Prime 798923 := by norm_num
private theorem prime_fortyAL_806041 : Nat.Prime 806041 := by norm_num
private theorem prime_fortyAL_827303 : Nat.Prime 827303 := by norm_num
private theorem prime_fortyAL_874459 : Nat.Prime 874459 := by norm_num
private theorem prime_fortyAL_878489 : Nat.Prime 878489 := by norm_num
private theorem prime_fortyAL_904369 : Nat.Prime 904369 := by norm_num
private theorem prime_fortyAL_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_fortyAL_1044397 : Nat.Prime 1044397 := by norm_num
private theorem prime_fortyAL_1099327 : Nat.Prime 1099327 := by norm_num
private theorem prime_fortyAL_1176529 : Nat.Prime 1176529 := by norm_num
private theorem prime_fortyAL_1198103 : Nat.Prime 1198103 := by norm_num
private theorem prime_fortyAL_1201729 : Nat.Prime 1201729 := by norm_num
private theorem prime_fortyAL_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_fortyAL_1314539 : Nat.Prime 1314539 := by norm_num
private theorem prime_fortyAL_1363189 : Nat.Prime 1363189 := by norm_num
private theorem prime_fortyAL_1427389 : Nat.Prime 1427389 := by norm_num
private theorem prime_fortyAL_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_fortyAL_1438279 : Nat.Prime 1438279 := by norm_num
private theorem prime_fortyAL_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_fortyAL_1552861 : Nat.Prime 1552861 := by norm_num
private theorem prime_fortyAL_1618091 : Nat.Prime 1618091 := by norm_num
private theorem prime_fortyAL_1719547 : Nat.Prime 1719547 := by norm_num
private theorem prime_fortyAL_1790917 : Nat.Prime 1790917 := by norm_num
private theorem prime_fortyAL_1836511 : Nat.Prime 1836511 := by norm_num
private theorem prime_fortyAL_1846283 : Nat.Prime 1846283 := by norm_num
private theorem prime_fortyAL_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fortyAL_2126213 : Nat.Prime 2126213 := by norm_num
private theorem prime_fortyAL_2223839 : Nat.Prime 2223839 := by norm_num
private theorem prime_fortyAL_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_fortyAL_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_fortyAL_2428859 : Nat.Prime 2428859 := by norm_num
private theorem prime_fortyAL_2530769 : Nat.Prime 2530769 := by norm_num
private theorem prime_fortyAL_2552059 : Nat.Prime 2552059 := by norm_num
private theorem prime_fortyAL_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fortyAL_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_fortyAL_3035453 : Nat.Prime 3035453 := by norm_num
private theorem prime_fortyAL_3073999 : Nat.Prime 3073999 := by norm_num
private theorem prime_fortyAL_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_fortyAL_3509741 : Nat.Prime 3509741 := by norm_num
private theorem prime_fortyAL_3539743 : Nat.Prime 3539743 := by norm_num
private theorem prime_fortyAL_3586771 : Nat.Prime 3586771 := by norm_num
private theorem prime_fortyAL_4203707 : Nat.Prime 4203707 := by norm_num
private theorem prime_fortyAL_4267007 : Nat.Prime 4267007 := by norm_num
private theorem prime_fortyAL_4315799 : Nat.Prime 4315799 := by norm_num
private theorem prime_fortyAL_4833779 : Nat.Prime 4833779 := by norm_num
private theorem prime_fortyAL_4924417 : Nat.Prime 4924417 := by norm_num
private theorem prime_fortyAL_5330309 : Nat.Prime 5330309 := by norm_num
private theorem prime_fortyAL_5365121 : Nat.Prime 5365121 := by norm_num
private theorem prime_fortyAL_6385741 : Nat.Prime 6385741 := by norm_num
private theorem prime_fortyAL_6562679 : Nat.Prime 6562679 := by norm_num
private theorem prime_fortyAL_6840413 : Nat.Prime 6840413 := by norm_num
private theorem prime_fortyAL_7041049 : Nat.Prime 7041049 := by norm_num
private theorem prime_fortyAL_7116059 : Nat.Prime 7116059 := by norm_num
private theorem prime_fortyAL_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyAL_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_fortyAL_7385153 : Nat.Prime 7385153 := by norm_num
private theorem prime_fortyAL_7746119 : Nat.Prime 7746119 := by norm_num
private theorem prime_fortyAL_7857071 : Nat.Prime 7857071 := by norm_num
private theorem prime_fortyAL_9047413 : Nat.Prime 9047413 := by norm_num
private theorem prime_fortyAL_9376751 : Nat.Prime 9376751 := by norm_num
private theorem prime_fortyAL_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_fortyAL_10876741 : Nat.Prime 10876741 := by norm_num
private theorem prime_fortyAL_11637001 : Nat.Prime 11637001 := by norm_num
private theorem prime_fortyAL_12633011 : Nat.Prime 12633011 := by norm_num
private theorem prime_fortyAL_12826067 : Nat.Prime 12826067 := by norm_num
private theorem prime_fortyAL_12909521 : Nat.Prime 12909521 := by norm_num
private theorem prime_fortyAL_13428977 : Nat.Prime 13428977 := by norm_num
private theorem prime_fortyAL_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_fortyAL_13813439 : Nat.Prime 13813439 := by norm_num
private theorem prime_fortyAL_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_fortyAL_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_fortyAL_15899287 : Nat.Prime 15899287 := by norm_num
private theorem prime_fortyAL_17344237 : Nat.Prime 17344237 := by norm_num
private theorem prime_fortyAL_17867137 : Nat.Prime 17867137 := by norm_num
private theorem prime_fortyAL_18337103 : Nat.Prime 18337103 := by norm_num
private theorem prime_fortyAL_18480383 : Nat.Prime 18480383 := by norm_num
private theorem prime_fortyAL_18510553 : Nat.Prime 18510553 := by norm_num
private theorem prime_fortyAL_19312207 : Nat.Prime 19312207 := by norm_num
private theorem prime_fortyAL_20068183 : Nat.Prime 20068183 := by norm_num
private theorem prime_fortyAL_22539437 : Nat.Prime 22539437 := by norm_num
private theorem prime_fortyAL_23255671 : Nat.Prime 23255671 := by norm_num
private theorem prime_fortyAL_23950417 : Nat.Prime 23950417 := by norm_num
private theorem prime_fortyAL_25331881 : Nat.Prime 25331881 := by norm_num
private theorem prime_fortyAL_25817069 : Nat.Prime 25817069 := by norm_num
private theorem prime_fortyAL_25991599 : Nat.Prime 25991599 := by norm_num
private theorem prime_fortyAL_26538257 : Nat.Prime 26538257 := by norm_num
private theorem prime_fortyAL_26619991 : Nat.Prime 26619991 := by norm_num
private theorem prime_fortyAL_27212041 : Nat.Prime 27212041 := by norm_num
private theorem prime_fortyAL_29654903 : Nat.Prime 29654903 := by norm_num

private theorem prime_fortyAL_30083567 : Nat.Prime 30083567 := by
  apply lucas_primality 30083567 (5 : ZMod 30083567)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1277, 1), (11779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1277, 1), (11779, 1)] : List FactorBlock).map factorBlockValue).prod) = 30083567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_1277
      · exact prime_fortyAL_11779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30083567) ^ 15041783 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 30083567) ^ 23558 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 30083567) ^ 2554 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_30126293 : Nat.Prime 30126293 := by
  apply lucas_primality 30126293 (2 : ZMod 30126293)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) = 30126293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_109
      · exact prime_fortyAL_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30126293) ^ 15063146 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 4303756 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 276388 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 3052 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_32364193 : Nat.Prime 32364193 := by
  apply lucas_primality 32364193 (15 : ZMod 32364193)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32364193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_17
      · exact prime_fortyAL_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32364193) ^ 16182096 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 10788064 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 4623456 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 1903776 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 11424 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_983
      · exact prime_fortyAL_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_40908451 : Nat.Prime 40908451 := by
  apply lucas_primality 40908451 (2 : ZMod 40908451)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) = 40908451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_24793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40908451) ^ 20454225 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 13636150 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 8181690 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 3718950 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 1650 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_42001217 : Nat.Prime 42001217 := by
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_37
      · exact prime_fortyAL_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42001217) ^ 21000608 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 1135168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 2368 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_43393043 : Nat.Prime 43393043 := by
  apply lucas_primality 43393043 (2 : ZMod 43393043)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (23, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (23, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) = 43393043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_23
      · exact prime_fortyAL_12251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43393043) ^ 21696521 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 6199006 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 3944822 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 1886654 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 3542 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_45377653 : Nat.Prime 45377653 := by
  apply lucas_primality 45377653 (2 : ZMod 45377653)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (149, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (149, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 45377653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_41
      · exact prime_fortyAL_149
      · exact prime_fortyAL_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45377653) ^ 22688826 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 45377653) ^ 15125884 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 45377653) ^ 1106772 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 45377653) ^ 304548 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 45377653) ^ 73308 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_51634139 : Nat.Prime 51634139 := by
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51634139) ^ 25817069 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 51634139) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_56624411 : Nat.Prime 56624411 := by
  apply lucas_primality 56624411 (2 : ZMod 56624411)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) = 56624411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_109
      · exact prime_fortyAL_51949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56624411) ^ 28312205 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 11324882 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 519490 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 1090 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_57889883 : Nat.Prime 57889883 := by
  apply lucas_primality 57889883 (2 : ZMod 57889883)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (353, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (353, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 57889883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_167
      · exact prime_fortyAL_353
      · exact prime_fortyAL_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57889883) ^ 28944941 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 346646 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 163994 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 117902 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_59738099 : Nat.Prime 59738099 := by
  apply lucas_primality 59738099 (2 : ZMod 59738099)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4267007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4267007, 1)] : List FactorBlock).map factorBlockValue).prod) = 59738099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_4267007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59738099) ^ 29869049 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 59738099) ^ 8534014 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 59738099) ^ 14 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_62963231 : Nat.Prime 62963231 := by
  apply lucas_primality 62963231 (7 : ZMod 62963231)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (73, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (73, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) = 62963231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_73
      · exact prime_fortyAL_7841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62963231) ^ 31481615 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 12592646 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 5723930 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 862510 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 8030 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_64381453 : Nat.Prime 64381453 := by
  apply lucas_primality 64381453 (2 : ZMod 64381453)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5365121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5365121, 1)] : List FactorBlock).map factorBlockValue).prod) = 64381453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5365121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64381453) ^ 32190726 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 64381453) ^ 21460484 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 64381453) ^ 12 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_66552427 : Nat.Prime 66552427 := by
  apply lucas_primality 66552427 (2 : ZMod 66552427)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1427, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1427, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) = 66552427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_1427
      · exact prime_fortyAL_2591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66552427) ^ 33276213 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 22184142 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 46638 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 25686 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_1901
      · exact prime_fortyAL_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_75335291 : Nat.Prime 75335291 := by
  apply lucas_primality 75335291 (2 : ZMod 75335291)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (271, 1), (27799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (271, 1), (27799, 1)] : List FactorBlock).map factorBlockValue).prod) = 75335291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_271
      · exact prime_fortyAL_27799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75335291) ^ 37667645 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 75335291) ^ 15067058 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 75335291) ^ 277990 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 75335291) ^ 2710 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_78786709 : Nat.Prime 78786709 := by
  apply lucas_primality 78786709 (6 : ZMod 78786709)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 78786709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 78786709) ^ 39393354 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 26262236 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 11255244 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 7162428 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 6060516 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 84084 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_82478129 : Nat.Prime 82478129 := by
  apply lucas_primality 82478129 (3 : ZMod 82478129)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (119881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (119881, 1)] : List FactorBlock).map factorBlockValue).prod) = 82478129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_43
      · exact prime_fortyAL_119881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 82478129) ^ 41239064 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 82478129) ^ 1918096 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 82478129) ^ 688 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_86786087 : Nat.Prime 86786087 := by
  apply lucas_primality 86786087 (5 : ZMod 86786087)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43393043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43393043, 1)] : List FactorBlock).map factorBlockValue).prod) = 86786087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_43393043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 86786087) ^ 43393043 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 86786087) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_23
      · exact prime_fortyAL_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_100888969 : Nat.Prime 100888969 := by
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100888969) ^ 50444484 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 33629656 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 24 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_105801979 : Nat.Prime 105801979 := by
  apply lucas_primality 105801979 (3 : ZMod 105801979)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 105801979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_23
      · exact prime_fortyAL_67
      · exact prime_fortyAL_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105801979) ^ 52900989 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 35267326 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 4600086 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 1579134 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 9246 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_19
      · exact prime_fortyAL_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_110421277 : Nat.Prime 110421277 := by
  apply lucas_primality 110421277 (2 : ZMod 110421277)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1314539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1314539, 1)] : List FactorBlock).map factorBlockValue).prod) = 110421277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_1314539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110421277) ^ 55210638 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 36807092 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 15774468 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 84 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_115779767 : Nat.Prime 115779767 := by
  apply lucas_primality 115779767 (5 : ZMod 115779767)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57889883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57889883, 1)] : List FactorBlock).map factorBlockValue).prod) = 115779767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_57889883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 115779767) ^ 57889883 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 115779767) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_124476641 : Nat.Prime 124476641 := by
  apply lucas_primality 124476641 (3 : ZMod 124476641)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (777979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (777979, 1)] : List FactorBlock).map factorBlockValue).prod) = 124476641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_777979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 124476641) ^ 62238320 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 124476641) ^ 24895328 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 124476641) ^ 160 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_126881009 : Nat.Prime 126881009 := by
  apply lucas_primality 126881009 (3 : ZMod 126881009)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) = 126881009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_73
      · exact prime_fortyAL_108631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126881009) ^ 63440504 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 126881009) ^ 1738096 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 126881009) ^ 1168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_135170359 : Nat.Prime 135170359 := by
  apply lucas_primality 135170359 (6 : ZMod 135170359)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135170359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_41
      · exact prime_fortyAL_163
      · exact prime_fortyAL_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135170359) ^ 67585179 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 45056786 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 3296838 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 829266 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 40098 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_144038591 : Nat.Prime 144038591 := by
  apply lucas_primality 144038591 (7 : ZMod 144038591)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 144038591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_827
      · exact prime_fortyAL_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144038591) ^ 72019295 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 28807718 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 174170 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 8270 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_144758609 : Nat.Prime 144758609 := by
  apply lucas_primality 144758609 (3 : ZMod 144758609)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (9047413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (9047413, 1)] : List FactorBlock).map factorBlockValue).prod) = 144758609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_9047413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 144758609) ^ 72379304 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 144758609) ^ 16 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_147061949 : Nat.Prime 147061949 := by
  apply lucas_primality 147061949 (3 : ZMod 147061949)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (311, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (311, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 147061949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_311
      · exact prime_fortyAL_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 147061949) ^ 73530974 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 147061949) ^ 13369268 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 147061949) ^ 472868 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 147061949) ^ 150524 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_163646341 : Nat.Prime 163646341 := by
  apply lucas_primality 163646341 (7 : ZMod 163646341)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) = 163646341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_19073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163646341) ^ 81823170 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 54548780 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 32729268 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 14876940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 12588180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 8580 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_167022307 : Nat.Prime 167022307 := by
  apply lucas_primality 167022307 (3 : ZMod 167022307)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (293, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (293, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 167022307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_293
      · exact prime_fortyAL_2879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 167022307) ^ 83511153 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 167022307) ^ 55674102 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 167022307) ^ 15183846 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 167022307) ^ 570042 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 167022307) ^ 58014 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_167470561 : Nat.Prime 167470561 := by
  apply lucas_primality 167470561 (13 : ZMod 167470561)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 167470561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_19
      · exact prime_fortyAL_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167470561) ^ 83735280 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 55823520 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 33494112 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 8814240 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 27360 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_177855893 : Nat.Prime 177855893 := by
  apply lucas_primality 177855893 (2 : ZMod 177855893)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (1201729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (1201729, 1)] : List FactorBlock).map factorBlockValue).prod) = 177855893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_37
      · exact prime_fortyAL_1201729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 177855893) ^ 88927946 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 177855893) ^ 4806916 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 177855893) ^ 148 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_178287611 : Nat.Prime 178287611 := by
  apply lucas_primality 178287611 (2 : ZMod 178287611)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (193, 1), (92377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (193, 1), (92377, 1)] : List FactorBlock).map factorBlockValue).prod) = 178287611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_193
      · exact prime_fortyAL_92377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 178287611) ^ 89143805 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 178287611) ^ 35657522 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 178287611) ^ 923770 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 178287611) ^ 1930 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_181510613 : Nat.Prime 181510613 := by
  apply lucas_primality 181510613 (2 : ZMod 181510613)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (45377653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (45377653, 1)] : List FactorBlock).map factorBlockValue).prod) = 181510613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_45377653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 181510613) ^ 90755306 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 181510613) ^ 4 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_181537789 : Nat.Prime 181537789 := by
  apply lucas_primality 181537789 (2 : ZMod 181537789)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1171, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1171, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 181537789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_1171
      · exact prime_fortyAL_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181537789) ^ 90768894 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 181537789) ^ 60512596 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 181537789) ^ 155028 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 181537789) ^ 14052 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_183514301 : Nat.Prime 183514301 := by
  apply lucas_primality 183514301 (2 : ZMod 183514301)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (97, 1), (18919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (97, 1), (18919, 1)] : List FactorBlock).map factorBlockValue).prod) = 183514301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_97
      · exact prime_fortyAL_18919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183514301) ^ 91757150 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 36702860 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 1891900 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 9700 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_193465039 : Nat.Prime 193465039 := by
  apply lucas_primality 193465039 (11 : ZMod 193465039)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (61, 1), (73, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (61, 1), (73, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 193465039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_61
      · exact prime_fortyAL_73
      · exact prime_fortyAL_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 193465039) ^ 96732519 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 193465039) ^ 64488346 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 193465039) ^ 14881926 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 193465039) ^ 3171558 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 193465039) ^ 2650206 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 193465039) ^ 347334 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_200447861 : Nat.Prime 200447861 := by
  apply lucas_primality 200447861 (2 : ZMod 200447861)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (271, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (271, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 200447861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_31
      · exact prime_fortyAL_271
      · exact prime_fortyAL_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200447861) ^ 100223930 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 40089572 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 6466060 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 739660 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 168020 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_219959393 : Nat.Prime 219959393 := by
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_67
      · exact prime_fortyAL_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219959393) ^ 109979696 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 3282976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 2144 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_225273263 : Nat.Prime 225273263 := by
  apply lucas_primality 225273263 (5 : ZMod 225273263)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) = 225273263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_223
      · exact prime_fortyAL_505097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225273263) ^ 112636631 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 1010194 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 446 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_191
      · exact prime_fortyAL_383
      · exact prime_fortyAL_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_240818197 : Nat.Prime 240818197 := by
  apply lucas_primality 240818197 (2 : ZMod 240818197)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20068183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20068183, 1)] : List FactorBlock).map factorBlockValue).prod) = 240818197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_20068183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 240818197) ^ 120409098 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 240818197) ^ 80272732 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 240818197) ^ 12 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_243906799 : Nat.Prime 243906799 := by
  apply lucas_primality 243906799 (3 : ZMod 243906799)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1321, 1), (30773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1321, 1), (30773, 1)] : List FactorBlock).map factorBlockValue).prod) = 243906799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_1321
      · exact prime_fortyAL_30773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 243906799) ^ 121953399 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 243906799) ^ 81302266 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 243906799) ^ 184638 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 243906799) ^ 7926 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_248953283 : Nat.Prime 248953283 := by
  apply lucas_primality 248953283 (2 : ZMod 248953283)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (124476641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (124476641, 1)] : List FactorBlock).map factorBlockValue).prod) = 248953283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_124476641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 248953283) ^ 124476641 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 248953283) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_274991737 : Nat.Prime 274991737 := by
  apply lucas_primality 274991737 (5 : ZMod 274991737)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (243787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (243787, 1)] : List FactorBlock).map factorBlockValue).prod) = 274991737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_47
      · exact prime_fortyAL_243787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 274991737) ^ 137495868 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 274991737) ^ 91663912 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 274991737) ^ 5850888 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 274991737) ^ 1128 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_67
      · exact prime_fortyAL_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_289267687 : Nat.Prime 289267687 := by
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 289267687) ^ 144633843 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 96422562 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 486 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_289517219 : Nat.Prime 289517219 := by
  apply lucas_primality 289517219 (2 : ZMod 289517219)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (144758609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (144758609, 1)] : List FactorBlock).map factorBlockValue).prod) = 289517219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_144758609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 289517219) ^ 144758609 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 289517219) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_304360757 : Nat.Prime 304360757 := by
  apply lucas_primality 304360757 (2 : ZMod 304360757)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1552861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1552861, 1)] : List FactorBlock).map factorBlockValue).prod) = 304360757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_1552861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 304360757) ^ 152180378 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 304360757) ^ 43480108 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 304360757) ^ 196 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_381624127 : Nat.Prime 381624127 := by
  apply lucas_primality 381624127 (3 : ZMod 381624127)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) = 381624127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_287801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 381624127) ^ 190812063 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 127208042 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 29355702 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 22448478 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 1326 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_490901413 : Nat.Prime 490901413 := by
  apply lucas_primality 490901413 (5 : ZMod 490901413)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40908451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40908451, 1)] : List FactorBlock).map factorBlockValue).prod) = 490901413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_40908451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 490901413) ^ 245450706 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 490901413) ^ 163633804 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 490901413) ^ 12 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_17
      · exact prime_fortyAL_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_503705849 : Nat.Prime 503705849 := by
  apply lucas_primality 503705849 (3 : ZMod 503705849)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (62963231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (62963231, 1)] : List FactorBlock).map factorBlockValue).prod) = 503705849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_62963231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 503705849) ^ 251852924 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 503705849) ^ 8 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_566837867 : Nat.Prime 566837867 := by
  apply lucas_primality 566837867 (2 : ZMod 566837867)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3413, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3413, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) = 566837867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_3413
      · exact prime_fortyAL_11863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 566837867) ^ 283418933 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 566837867) ^ 80976838 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 566837867) ^ 166082 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 566837867) ^ 47782 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_569284721 : Nat.Prime 569284721 := by
  apply lucas_primality 569284721 (3 : ZMod 569284721)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7116059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7116059, 1)] : List FactorBlock).map factorBlockValue).prod) = 569284721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7116059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 569284721) ^ 284642360 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 569284721) ^ 113856944 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 569284721) ^ 80 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_617236267 : Nat.Prime 617236267 := by
  apply lucas_primality 617236267 (2 : ZMod 617236267)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3229, 1), (31859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3229, 1), (31859, 1)] : List FactorBlock).map factorBlockValue).prod) = 617236267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_3229
      · exact prime_fortyAL_31859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 617236267) ^ 308618133 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 617236267) ^ 205745422 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 617236267) ^ 191154 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 617236267) ^ 19374 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_889647091 : Nat.Prime 889647091 := by
  apply lucas_primality 889647091 (3 : ZMod 889647091)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) = 889647091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_29654903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 889647091) ^ 444823545 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 296549030 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 177929418 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 30 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_928715773 : Nat.Prime 928715773 := by
  apply lucas_primality 928715773 (2 : ZMod 928715773)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (673, 1), (114997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (673, 1), (114997, 1)] : List FactorBlock).map factorBlockValue).prod) = 928715773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_673
      · exact prime_fortyAL_114997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 928715773) ^ 464357886 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 309571924 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 1379964 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 8076 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_984401851 : Nat.Prime 984401851 := by
  apply lucas_primality 984401851 (2 : ZMod 984401851)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (6562679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (6562679, 1)] : List FactorBlock).map factorBlockValue).prod) = 984401851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_6562679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 984401851) ^ 492200925 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 984401851) ^ 328133950 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 984401851) ^ 196880370 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 984401851) ^ 150 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1088621057 : Nat.Prime 1088621057 := by
  apply lucas_primality 1088621057 (3 : ZMod 1088621057)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088621057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_2126213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1088621057) ^ 544310528 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1088621057) ^ 512 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1147132367 : Nat.Prime 1147132367 := by
  apply lucas_primality 1147132367 (5 : ZMod 1147132367)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (7857071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (7857071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1147132367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_73
      · exact prime_fortyAL_7857071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1147132367) ^ 573566183 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147132367) ^ 15714142 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147132367) ^ 146 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_29
      · exact prime_fortyAL_113
      · exact prime_fortyAL_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_61
      · exact prime_fortyAL_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1526496509 : Nat.Prime 1526496509 := by
  apply lucas_primality 1526496509 (2 : ZMod 1526496509)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1526496509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_381624127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1526496509) ^ 763248254 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526496509) ^ 4 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1592295421 : Nat.Prime 1592295421 := by
  apply lucas_primality 1592295421 (2 : ZMod 1592295421)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (26538257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (26538257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1592295421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_26538257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1592295421) ^ 796147710 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592295421) ^ 530765140 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592295421) ^ 318459084 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592295421) ^ 60 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1596046247 : Nat.Prime 1596046247 := by
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_19
      · exact prime_fortyAL_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1596046247) ^ 798023123 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 84002434 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 38 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1597258249 : Nat.Prime 1597258249 := by
  apply lucas_primality 1597258249 (7 : ZMod 1597258249)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (66552427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (66552427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597258249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_66552427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1597258249) ^ 798629124 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1597258249) ^ 532419416 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1597258249) ^ 24 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1656564227 : Nat.Prime 1656564227 := by
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_101
      · exact prime_fortyAL_2521
      · exact prime_fortyAL_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1656564227) ^ 828282113 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 16401626 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 657106 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 509242 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1678890277 : Nat.Prime 1678890277 := by
  apply lucas_primality 1678890277 (2 : ZMod 1678890277)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (101, 1), (65963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (101, 1), (65963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678890277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_101
      · exact prime_fortyAL_65963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1678890277) ^ 839445138 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678890277) ^ 559630092 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678890277) ^ 239841468 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678890277) ^ 16622676 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678890277) ^ 25452 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1827037183 : Nat.Prime 1827037183 := by
  apply lucas_primality 1827037183 (3 : ZMod 1827037183)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (881, 1), (345637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (881, 1), (345637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1827037183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_881
      · exact prime_fortyAL_345637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1827037183) ^ 913518591 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1827037183) ^ 609012394 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1827037183) ^ 2073822 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1827037183) ^ 5286 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_89
      · exact prime_fortyAL_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_61
      · exact prime_fortyAL_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2628498527 : Nat.Prime 2628498527 := by
  apply lucas_primality 2628498527 (5 : ZMod 2628498527)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (18510553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (18510553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2628498527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_71
      · exact prime_fortyAL_18510553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2628498527) ^ 1314249263 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 2628498527) ^ 37021106 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 2628498527) ^ 142 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_3463003639 : Nat.Prime 3463003639 := by
  apply lucas_primality 3463003639 (6 : ZMod 3463003639)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (73, 1), (878489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (73, 1), (878489, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463003639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_73
      · exact prime_fortyAL_878489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3463003639) ^ 1731501819 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463003639) ^ 1154334546 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463003639) ^ 47438406 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463003639) ^ 3942 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4744796093 : Nat.Prime 4744796093 := by
  apply lucas_primality 4744796093 (2 : ZMod 4744796093)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3673, 1), (322951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3673, 1), (322951, 1)] : List FactorBlock).map factorBlockValue).prod) = 4744796093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3673
      · exact prime_fortyAL_322951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4744796093) ^ 2372398046 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4744796093) ^ 1291804 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4744796093) ^ 14692 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_6389032997 : Nat.Prime 6389032997 := by
  apply lucas_primality 6389032997 (2 : ZMod 6389032997)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1597258249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1597258249, 1)] : List FactorBlock).map factorBlockValue).prod) = 6389032997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_1597258249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6389032997) ^ 3194516498 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 6389032997) ^ 4 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7062967943 : Nat.Prime 7062967943 := by
  apply lucas_primality 7062967943 (5 : ZMod 7062967943)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) = 7062967943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5479
      · exact prime_fortyAL_644549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7062967943) ^ 3531483971 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 1289098 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 10958 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7647016217 : Nat.Prime 7647016217 := by
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_7549
      · exact prime_fortyAL_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7647016217) ^ 3823508108 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1092430888 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1012984 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 422744 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7766497153 : Nat.Prime 7766497153 := by
  apply lucas_primality 7766497153 (10 : ZMod 7766497153)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (19, 1), (354829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (19, 1), (354829, 1)] : List FactorBlock).map factorBlockValue).prod) = 7766497153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_19
      · exact prime_fortyAL_354829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 7766497153) ^ 3883248576 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 7766497153) ^ 2588832384 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 7766497153) ^ 408763008 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 7766497153) ^ 21888 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7935730139 : Nat.Prime 7935730139 := by
  apply lucas_primality 7935730139 (2 : ZMod 7935730139)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (566837867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (566837867, 1)] : List FactorBlock).map factorBlockValue).prod) = 7935730139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_566837867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7935730139) ^ 3967865069 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 7935730139) ^ 1133675734 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 7935730139) ^ 14 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_8408707693 : Nat.Prime 8408707693 := by
  apply lucas_primality 8408707693 (15 : ZMod 8408707693)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 2), (827303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 2), (827303, 1)] : List FactorBlock).map factorBlockValue).prod) = 8408707693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_827303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 8408707693) ^ 4204353846 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 2802902564 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 1201243956 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 764427972 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 10164 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_10855569737 : Nat.Prime 10855569737 := by
  apply lucas_primality 10855569737 (5 : ZMod 10855569737)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (139, 1), (809, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (139, 1), (809, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 10855569737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_139
      · exact prime_fortyAL_809
      · exact prime_fortyAL_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10855569737) ^ 5427784868 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 986869976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 78097624 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 13418504 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 9895688 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_10892708831 : Nat.Prime 10892708831 := by
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_43
      · exact prime_fortyAL_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10892708831) ^ 5446354415 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 2178541766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 253318810 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 430 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11673052829 : Nat.Prime 11673052829 := by
  apply lucas_primality 11673052829 (3 : ZMod 11673052829)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (126881009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (126881009, 1)] : List FactorBlock).map factorBlockValue).prod) = 11673052829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_23
      · exact prime_fortyAL_126881009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11673052829) ^ 5836526414 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 11673052829) ^ 507524036 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 11673052829) ^ 92 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_15383
      · exact prime_fortyAL_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_13525563643 : Nat.Prime 13525563643 := by
  apply lucas_primality 13525563643 (2 : ZMod 13525563643)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (571, 1), (74489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (571, 1), (74489, 1)] : List FactorBlock).map factorBlockValue).prod) = 13525563643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_53
      · exact prime_fortyAL_571
      · exact prime_fortyAL_74489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13525563643) ^ 6762781821 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13525563643) ^ 4508521214 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13525563643) ^ 255199314 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13525563643) ^ 23687502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13525563643) ^ 181578 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_349
      · exact prime_fortyAL_619
      · exact prime_fortyAL_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_14296463171 : Nat.Prime 14296463171 := by
  apply lucas_primality 14296463171 (2 : ZMod 14296463171)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (6840413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (6840413, 1)] : List FactorBlock).map factorBlockValue).prod) = 14296463171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_19
      · exact prime_fortyAL_6840413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14296463171) ^ 7148231585 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 14296463171) ^ 2859292634 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 14296463171) ^ 1299678470 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 14296463171) ^ 752445430 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 14296463171) ^ 2090 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_15040590709 : Nat.Prime 15040590709 := by
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_311
      · exact prime_fortyAL_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15040590709) ^ 7520295354 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 5013530236 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1367326428 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1156968516 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 48362028 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 533676 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_15173528663 : Nat.Prime 15173528663 := by
  apply lucas_primality 15173528663 (5 : ZMod 15173528663)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22973, 1), (330247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22973, 1), (330247, 1)] : List FactorBlock).map factorBlockValue).prod) = 15173528663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_22973
      · exact prime_fortyAL_330247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15173528663) ^ 7586764331 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 15173528663) ^ 660494 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 15173528663) ^ 45946 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_16698976397 : Nat.Prime 16698976397 := by
  apply lucas_primality 16698976397 (2 : ZMod 16698976397)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (181510613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (181510613, 1)] : List FactorBlock).map factorBlockValue).prod) = 16698976397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_23
      · exact prime_fortyAL_181510613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16698976397) ^ 8349488198 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 16698976397) ^ 726042452 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 16698976397) ^ 92 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_17755350889 : Nat.Prime 17755350889 := by
  apply lucas_primality 17755350889 (14 : ZMod 17755350889)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) = 17755350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_19
      · exact prime_fortyAL_3539743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17755350889) ^ 8877675444 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5918450296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 1614122808 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 934492152 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5016 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_18554151617 : Nat.Prime 18554151617 := by
  apply lucas_primality 18554151617 (5 : ZMod 18554151617)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 2), (13, 1), (113, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 2), (13, 1), (113, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 18554151617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_113
      · exact prime_fortyAL_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18554151617) ^ 9277075808 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18554151617) ^ 2650593088 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18554151617) ^ 1686741056 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18554151617) ^ 1427242432 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18554151617) ^ 164196032 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18554151617) ^ 79631552 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_21951611911 : Nat.Prime 21951611911 := by
  apply lucas_primality 21951611911 (12 : ZMod 21951611911)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (243906799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (243906799, 1)] : List FactorBlock).map factorBlockValue).prod) = 21951611911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_243906799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 21951611911) ^ 10975805955 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (12 : ZMod 21951611911) ^ 7317203970 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (12 : ZMod 21951611911) ^ 4390322382 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (12 : ZMod 21951611911) ^ 90 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_23959559521 : Nat.Prime 23959559521 := by
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_13
      · exact prime_fortyAL_191
      · exact prime_fortyAL_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23959559521) ^ 11979779760 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 7986519840 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 4791911904 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 1843043040 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 125442720 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 3575520 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_24330664621 : Nat.Prime 24330664621 := by
  apply lucas_primality 24330664621 (2 : ZMod 24330664621)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) = 24330664621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_135170359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24330664621) ^ 12165332310 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 8110221540 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 4866132924 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_31
      · exact prime_fortyAL_71
      · exact prime_fortyAL_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_17
      · exact prime_fortyAL_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_29053740073 : Nat.Prime 29053740073 := by
  apply lucas_primality 29053740073 (10 : ZMod 29053740073)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (113, 1), (499, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (113, 1), (499, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 29053740073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_113
      · exact prime_fortyAL_499
      · exact prime_fortyAL_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 29053740073) ^ 14526870036 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 29053740073) ^ 9684580024 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 29053740073) ^ 4150534296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 29053740073) ^ 257112744 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 29053740073) ^ 58223928 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 29053740073) ^ 9473016 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_30569989673 : Nat.Prime 30569989673 := by
  apply lucas_primality 30569989673 (3 : ZMod 30569989673)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4783, 1), (798923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4783, 1), (798923, 1)] : List FactorBlock).map factorBlockValue).prod) = 30569989673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_4783
      · exact prime_fortyAL_798923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30569989673) ^ 15284994836 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 30569989673) ^ 6391384 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 30569989673) ^ 38264 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_151
      · exact prime_fortyAL_479
      · exact prime_fortyAL_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_51033940343 : Nat.Prime 51033940343 := by
  apply lucas_primality 51033940343 (10 : ZMod 51033940343)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) = 51033940343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_30126293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51033940343) ^ 25516970171 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 7290562906 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 4639449122 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 1694 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_52555595681 : Nat.Prime 52555595681 := by
  apply lucas_primality 52555595681 (6 : ZMod 52555595681)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (29, 1), (1618091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (29, 1), (1618091, 1)] : List FactorBlock).map factorBlockValue).prod) = 52555595681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_29
      · exact prime_fortyAL_1618091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 52555595681) ^ 26277797840 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 52555595681) ^ 10511119136 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 52555595681) ^ 7507942240 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 52555595681) ^ 1812261920 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 52555595681) ^ 32480 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_61139979347 : Nat.Prime 61139979347 := by
  apply lucas_primality 61139979347 (2 : ZMod 61139979347)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30569989673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30569989673, 1)] : List FactorBlock).map factorBlockValue).prod) = 61139979347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_30569989673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 61139979347) ^ 30569989673 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 61139979347) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_63083964649 : Nat.Prime 63083964649 := by
  apply lucas_primality 63083964649 (7 : ZMod 63083964649)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2628498527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2628498527, 1)] : List FactorBlock).map factorBlockValue).prod) = 63083964649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_2628498527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 63083964649) ^ 31541982324 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 63083964649) ^ 21027988216 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 63083964649) ^ 24 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_76085543257 : Nat.Prime 76085543257 := by
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_2221
      · exact prime_fortyAL_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76085543257) ^ 38042771628 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 25361847752 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 34257336 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 53304 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_102067880687 : Nat.Prime 102067880687 := by
  apply lucas_primality 102067880687 (5 : ZMod 102067880687)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) = 102067880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_51033940343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 102067880687) ^ 51033940343 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 102067880687) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_113304743063 : Nat.Prime 113304743063 := by
  apply lucas_primality 113304743063 (5 : ZMod 113304743063)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (331, 1), (1438279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (331, 1), (1438279, 1)] : List FactorBlock).map factorBlockValue).prod) = 113304743063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_17
      · exact prime_fortyAL_331
      · exact prime_fortyAL_1438279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 113304743063) ^ 56652371531 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 113304743063) ^ 16186391866 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 113304743063) ^ 6664984886 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 113304743063) ^ 342310402 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 113304743063) ^ 78778 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_141780919669 : Nat.Prime 141780919669 := by
  apply lucas_primality 141780919669 (2 : ZMod 141780919669)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (110421277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (110421277, 1)] : List FactorBlock).map factorBlockValue).prod) = 141780919669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_107
      · exact prime_fortyAL_110421277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 141780919669) ^ 70890459834 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 47260306556 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 1325055324 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 1284 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_159097227851 : Nat.Prime 159097227851 := by
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159097227851) ^ 79548613925 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 31819445570 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 14463384350 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 550 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_200270135539 : Nat.Prime 200270135539 := by
  apply lucas_primality 200270135539 (2 : ZMod 200270135539)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (89, 1), (139, 1), (81761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (89, 1), (139, 1), (81761, 1)] : List FactorBlock).map factorBlockValue).prod) = 200270135539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_89
      · exact prime_fortyAL_139
      · exact prime_fortyAL_81761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200270135539) ^ 100135067769 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200270135539) ^ 66756711846 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200270135539) ^ 18206375958 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200270135539) ^ 2250226242 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200270135539) ^ 1440792342 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 200270135539) ^ 2449458 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_219613389623 : Nat.Prime 219613389623 := by
  apply lucas_primality 219613389623 (5 : ZMod 219613389623)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) = 219613389623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_61
      · exact prime_fortyAL_163646341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 219613389623) ^ 109806694811 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 19964853602 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 3600219502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 1342 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_237841108607 : Nat.Prime 237841108607 := by
  apply lucas_primality 237841108607 (5 : ZMod 237841108607)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) = 237841108607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_31
      · exact prime_fortyAL_1093
      · exact prime_fortyAL_3509741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237841108607) ^ 118920554303 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 7672293826 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 217603942 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 67766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_246470474641 : Nat.Prime 246470474641 := by
  apply lucas_primality 246470474641 (21 : ZMod 246470474641)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (1973, 1), (40039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (1973, 1), (40039, 1)] : List FactorBlock).map factorBlockValue).prod) = 246470474641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_13
      · exact prime_fortyAL_1973
      · exact prime_fortyAL_40039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 246470474641) ^ 123235237320 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 246470474641) ^ 82156824880 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 246470474641) ^ 49294094928 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 246470474641) ^ 18959267280 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 246470474641) ^ 124921680 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 246470474641) ^ 6155760 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_249951341833 : Nat.Prime 249951341833 := by
  apply lucas_primality 249951341833 (5 : ZMod 249951341833)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (73, 1), (3035453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (73, 1), (3035453, 1)] : List FactorBlock).map factorBlockValue).prod) = 249951341833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_47
      · exact prime_fortyAL_73
      · exact prime_fortyAL_3035453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 249951341833) ^ 124975670916 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 83317113944 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 5318113656 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 3423990984 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 82344 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_309443352821 : Nat.Prime 309443352821 := by
  apply lucas_primality 309443352821 (2 : ZMod 309443352821)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (37, 1), (59738099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (37, 1), (59738099, 1)] : List FactorBlock).map factorBlockValue).prod) = 309443352821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_37
      · exact prime_fortyAL_59738099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 309443352821) ^ 154721676410 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 61888670564 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 44206193260 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 8363333860 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 5180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_315158973341 : Nat.Prime 315158973341 := by
  apply lucas_primality 315158973341 (10 : ZMod 315158973341)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (1487, 1), (119069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (1487, 1), (119069, 1)] : List FactorBlock).map factorBlockValue).prod) = 315158973341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_89
      · exact prime_fortyAL_1487
      · exact prime_fortyAL_119069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 315158973341) ^ 157579486670 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 315158973341) ^ 63031794668 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 315158973341) ^ 3541112060 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 315158973341) ^ 211942820 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 315158973341) ^ 2646860 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_320918551601 : Nat.Prime 320918551601 := by
  apply lucas_primality 320918551601 (3 : ZMod 320918551601)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (71, 1), (107, 1), (105607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (71, 1), (107, 1), (105607, 1)] : List FactorBlock).map factorBlockValue).prod) = 320918551601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_71
      · exact prime_fortyAL_107
      · exact prime_fortyAL_105607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 320918551601) ^ 160459275800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 320918551601) ^ 64183710320 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 320918551601) ^ 4519979600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 320918551601) ^ 2999238800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 320918551601) ^ 3038800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_347522114119 : Nat.Prime 347522114119 := by
  apply lucas_primality 347522114119 (3 : ZMod 347522114119)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (61, 1), (149, 1), (199, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (61, 1), (149, 1), (199, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 347522114119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_31
      · exact prime_fortyAL_61
      · exact prime_fortyAL_149
      · exact prime_fortyAL_199
      · exact prime_fortyAL_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 347522114119) ^ 173761057059 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 115840704706 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 11210390778 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 5697083838 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 2332363182 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 1746342282 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 347522114119) ^ 336420246 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_366921263173 : Nat.Prime 366921263173 := by
  apply lucas_primality 366921263173 (5 : ZMod 366921263173)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (105801979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (105801979, 1)] : List FactorBlock).map factorBlockValue).prod) = 366921263173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_17
      · exact prime_fortyAL_105801979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 366921263173) ^ 183460631586 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 122307087724 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 21583603716 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 3468 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_390056504429 : Nat.Prime 390056504429 := by
  apply lucas_primality 390056504429 (2 : ZMod 390056504429)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) = 390056504429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_677
      · exact prime_fortyAL_144038591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390056504429) ^ 195028252214 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 576154364 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 2708 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_423119830387 : Nat.Prime 423119830387 := by
  apply lucas_primality 423119830387 (3 : ZMod 423119830387)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5449, 1), (1176529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5449, 1), (1176529, 1)] : List FactorBlock).map factorBlockValue).prod) = 423119830387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_5449
      · exact prime_fortyAL_1176529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 423119830387) ^ 211559915193 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 423119830387) ^ 141039943462 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 423119830387) ^ 38465439126 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 423119830387) ^ 77650914 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 423119830387) ^ 359634 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_17
      · exact prime_fortyAL_397
      · exact prime_fortyAL_2531
      · exact prime_fortyAL_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_578179136237 : Nat.Prime 578179136237 := by
  apply lucas_primality 578179136237 (2 : ZMod 578179136237)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (173, 1), (719, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (173, 1), (719, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod) = 578179136237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_13
      · exact prime_fortyAL_71
      · exact prime_fortyAL_173
      · exact prime_fortyAL_719
      · exact prime_fortyAL_1259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 578179136237) ^ 289089568118 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 578179136237) ^ 44475318172 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 578179136237) ^ 8143368116 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 578179136237) ^ 3342075932 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 578179136237) ^ 804143444 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 578179136237) ^ 459236804 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_630317946683 : Nat.Prime 630317946683 := by
  apply lucas_primality 630317946683 (2 : ZMod 630317946683)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (315158973341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (315158973341, 1)] : List FactorBlock).map factorBlockValue).prod) = 630317946683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_315158973341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 630317946683) ^ 315158973341 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 630317946683) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_946000722259 : Nat.Prime 946000722259 := by
  apply lucas_primality 946000722259 (2 : ZMod 946000722259)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (52555595681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (52555595681, 1)] : List FactorBlock).map factorBlockValue).prod) = 946000722259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_52555595681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 946000722259) ^ 473000361129 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 946000722259) ^ 315333574086 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 946000722259) ^ 18 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_946789455011 : Nat.Prime 946789455011 := by
  apply lucas_primality 946789455011 (2 : ZMod 946789455011)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13525563643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13525563643, 1)] : List FactorBlock).map factorBlockValue).prod) = 946789455011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_13525563643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 946789455011) ^ 473394727505 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 946789455011) ^ 189357891002 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 946789455011) ^ 135255636430 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 946789455011) ^ 70 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_952287616681 : Nat.Prime 952287616681 := by
  apply lucas_primality 952287616681 (17 : ZMod 952287616681)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7935730139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7935730139, 1)] : List FactorBlock).map factorBlockValue).prod) = 952287616681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7935730139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 952287616681) ^ 476143808340 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 952287616681) ^ 317429205560 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 952287616681) ^ 190457523336 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 952287616681) ^ 120 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_999378217637 : Nat.Prime 999378217637 := by
  apply lucas_primality 999378217637 (2 : ZMod 999378217637)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (1033, 1), (1846283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (1033, 1), (1846283, 1)] : List FactorBlock).map factorBlockValue).prod) = 999378217637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_131
      · exact prime_fortyAL_1033
      · exact prime_fortyAL_1846283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 999378217637) ^ 499689108818 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 999378217637) ^ 7628841356 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 999378217637) ^ 967452292 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 999378217637) ^ 541292 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1013900596351 : Nat.Prime 1013900596351 := by
  apply lucas_primality 1013900596351 (3 : ZMod 1013900596351)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (31, 1), (12826067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (31, 1), (12826067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013900596351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_17
      · exact prime_fortyAL_31
      · exact prime_fortyAL_12826067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1013900596351) ^ 506950298175 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 337966865450 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 202780119270 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 59641211550 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 32706470850 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 79050 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1272241326337 : Nat.Prime 1272241326337 := by
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1272241326337) ^ 636120663168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 424080442112 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 768 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_397
      · exact prime_fortyAL_977
      · exact prime_fortyAL_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1464864774119 : Nat.Prime 1464864774119 := by
  apply lucas_primality 1464864774119 (13 : ZMod 1464864774119)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (1733, 1), (2530769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (1733, 1), (2530769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1464864774119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_167
      · exact prime_fortyAL_1733
      · exact prime_fortyAL_2530769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1464864774119) ^ 732432387059 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 1464864774119) ^ 8771645354 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 1464864774119) ^ 845276846 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 1464864774119) ^ 578822 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1483112670203 : Nat.Prime 1483112670203 := by
  apply lucas_primality 1483112670203 (2 : ZMod 1483112670203)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483112670203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_23
      · exact prime_fortyAL_30871
      · exact prime_fortyAL_1044397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483112670203) ^ 741556335101 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 64483159574 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 48042262 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 1420066 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_35279
      · exact prime_fortyAL_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1529752406099 : Nat.Prime 1529752406099 := by
  apply lucas_primality 1529752406099 (2 : ZMod 1529752406099)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1529752406099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_47
      · exact prime_fortyAL_89
      · exact prime_fortyAL_617
      · exact prime_fortyAL_42337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1529752406099) ^ 764876203049 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 218536058014 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 32547923534 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 17188229282 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 2479339394 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 36132754 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1743613808569 : Nat.Prime 1743613808569 := by
  apply lucas_primality 1743613808569 (7 : ZMod 1743613808569)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (367, 1), (6385741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (367, 1), (6385741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1743613808569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_31
      · exact prime_fortyAL_367
      · exact prime_fortyAL_6385741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1743613808569) ^ 871806904284 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743613808569) ^ 581204602856 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743613808569) ^ 56245606728 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743613808569) ^ 4750991304 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743613808569) ^ 273048 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1982473007243 : Nat.Prime 1982473007243 := by
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_13
      · exact prime_fortyAL_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1982473007243) ^ 991236503621 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 283210429606 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 152497923634 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 182 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_761
      · exact prime_fortyAL_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_3486448808761 : Nat.Prime 3486448808761 := by
  apply lucas_primality 3486448808761 (11 : ZMod 3486448808761)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (29053740073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (29053740073, 1)] : List FactorBlock).map factorBlockValue).prod) = 3486448808761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_29053740073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3486448808761) ^ 1743224404380 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 3486448808761) ^ 1162149602920 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 3486448808761) ^ 697289761752 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 3486448808761) ^ 120 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_3687861576799 : Nat.Prime 3687861576799 := by
  apply lucas_primality 3687861576799 (3 : ZMod 3687861576799)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (44647, 1), (655559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (44647, 1), (655559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687861576799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_44647
      · exact prime_fortyAL_655559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687861576799) ^ 1843930788399 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 1229287192266 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 526837368114 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 82600434 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 5625522 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4603831309349 : Nat.Prime 4603831309349 := by
  apply lucas_primality 4603831309349 (2 : ZMod 4603831309349)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1549, 1), (1787, 1), (415799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1549, 1), (1787, 1), (415799, 1)] : List FactorBlock).map factorBlockValue).prod) = 4603831309349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_1549
      · exact prime_fortyAL_1787
      · exact prime_fortyAL_415799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4603831309349) ^ 2301915654674 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4603831309349) ^ 2972131252 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4603831309349) ^ 2576290604 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4603831309349) ^ 11072252 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4605794839871 : Nat.Prime 4605794839871 := by
  apply lucas_primality 4605794839871 (7 : ZMod 4605794839871)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (3463003639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (3463003639, 1)] : List FactorBlock).map factorBlockValue).prod) = 4605794839871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_19
      · exact prime_fortyAL_3463003639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4605794839871) ^ 2302897419935 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 4605794839871) ^ 921158967974 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 4605794839871) ^ 657970691410 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 4605794839871) ^ 242410254730 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 4605794839871) ^ 1330 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_381559
      · exact prime_fortyAL_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5454939871309 : Nat.Prime 5454939871309 := by
  apply lucas_primality 5454939871309 (6 : ZMod 5454939871309)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61553, 1), (7385153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61553, 1), (7385153, 1)] : List FactorBlock).map factorBlockValue).prod) = 5454939871309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_61553
      · exact prime_fortyAL_7385153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5454939871309) ^ 2727469935654 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5454939871309) ^ 1818313290436 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5454939871309) ^ 88621836 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5454939871309) ^ 738636 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5502598141231 : Nat.Prime 5502598141231 := by
  apply lucas_primality 5502598141231 (6 : ZMod 5502598141231)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61139979347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61139979347, 1)] : List FactorBlock).map factorBlockValue).prod) = 5502598141231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_61139979347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5502598141231) ^ 2751299070615 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 1834199380410 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 1100519628246 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 90 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5934672374047 : Nat.Prime 5934672374047 := by
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934672374047) ^ 2967336187023 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 1978224124682 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 456513259542 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 78 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5996269305823 : Nat.Prime 5996269305823 := by
  apply lucas_primality 5996269305823 (6 : ZMod 5996269305823)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (999378217637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (999378217637, 1)] : List FactorBlock).map factorBlockValue).prod) = 5996269305823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_999378217637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5996269305823) ^ 2998134652911 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5996269305823) ^ 1998756435274 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 5996269305823) ^ 6 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_8340530738857 : Nat.Prime 8340530738857 := by
  apply lucas_primality 8340530738857 (5 : ZMod 8340530738857)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (347522114119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (347522114119, 1)] : List FactorBlock).map factorBlockValue).prod) = 8340530738857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_347522114119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8340530738857) ^ 4170265369428 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 8340530738857) ^ 2780176912952 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 8340530738857) ^ 24 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11680677399577 : Nat.Prime 11680677399577 := by
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_23
      · exact prime_fortyAL_79
      · exact prime_fortyAL_397
      · exact prime_fortyAL_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11680677399577) ^ 5840338699788 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 3893559133192 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 507855539112 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 147856675944 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 29422361208 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 17312376 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_13327406448887 : Nat.Prime 13327406448887 := by
  apply lucas_primality 13327406448887 (5 : ZMod 13327406448887)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (141780919669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (141780919669, 1)] : List FactorBlock).map factorBlockValue).prod) = 13327406448887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_47
      · exact prime_fortyAL_141780919669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13327406448887) ^ 6663703224443 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 13327406448887) ^ 283561839338 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 13327406448887) ^ 94 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_13443454509487 : Nat.Prime 13443454509487 := by
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_293
      · exact prime_fortyAL_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13443454509487) ^ 6721727254743 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 4481151503162 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 45882097302 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 1758 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_14751446307197 : Nat.Prime 14751446307197 := by
  apply lucas_primality 14751446307197 (2 : ZMod 14751446307197)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3687861576799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3687861576799, 1)] : List FactorBlock).map factorBlockValue).prod) = 14751446307197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3687861576799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14751446307197) ^ 7375723153598 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 14751446307197) ^ 4 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_16167034690327 : Nat.Prime 16167034690327 := by
  apply lucas_primality 16167034690327 (3 : ZMod 16167034690327)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (227, 1), (304360757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (227, 1), (304360757, 1)] : List FactorBlock).map factorBlockValue).prod) = 16167034690327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_227
      · exact prime_fortyAL_304360757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16167034690327) ^ 8083517345163 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 16167034690327) ^ 5389011563442 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 16167034690327) ^ 1243618053102 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 16167034690327) ^ 71220417138 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 16167034690327) ^ 53118 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_16304803331431 : Nat.Prime 16304803331431 := by
  apply lucas_primality 16304803331431 (21 : ZMod 16304803331431)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (24113, 1), (22539437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (24113, 1), (22539437, 1)] : List FactorBlock).map factorBlockValue).prod) = 16304803331431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_24113
      · exact prime_fortyAL_22539437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 16304803331431) ^ 8152401665715 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 16304803331431) ^ 5434934443810 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 16304803331431) ^ 3260960666286 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 16304803331431) ^ 676183110 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (21 : ZMod 16304803331431) ^ 723390 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_18844061505463 : Nat.Prime 18844061505463 := by
  apply lucas_primality 18844061505463 (5 : ZMod 18844061505463)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (191, 1), (1827037183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (191, 1), (1827037183, 1)] : List FactorBlock).map factorBlockValue).prod) = 18844061505463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_191
      · exact prime_fortyAL_1827037183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18844061505463) ^ 9422030752731 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18844061505463) ^ 6281353835154 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18844061505463) ^ 98660007882 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 18844061505463) ^ 10314 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_36209809875559 : Nat.Prime 36209809875559 := by
  apply lucas_primality 36209809875559 (3 : ZMod 36209809875559)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (47, 1), (11673052829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (47, 1), (11673052829, 1)] : List FactorBlock).map factorBlockValue).prod) = 36209809875559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_47
      · exact prime_fortyAL_11673052829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36209809875559) ^ 18104904937779 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 12069936625186 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 3291800897778 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 770421486714 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 3102 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_45820001621089 : Nat.Prime 45820001621089 := by
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 45820001621089) ^ 22910000810544 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 15273333873696 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 288 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_89
      · exact prime_fortyAL_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_69469166481151 : Nat.Prime 69469166481151 := by
  apply lucas_primality 69469166481151 (3 : ZMod 69469166481151)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (73, 1), (199, 1), (1099327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (73, 1), (199, 1), (1099327, 1)] : List FactorBlock).map factorBlockValue).prod) = 69469166481151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_29
      · exact prime_fortyAL_73
      · exact prime_fortyAL_199
      · exact prime_fortyAL_1099327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69469166481151) ^ 34734583240575 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 23156388827050 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 13893833296230 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 2395488499350 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 951632417550 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 349091288850 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 69469166481151) ^ 63192450 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_92795842518553 : Nat.Prime 92795842518553 := by
  apply lucas_primality 92795842518553 (5 : ZMod 92795842518553)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (31, 1), (167, 1), (248953283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (31, 1), (167, 1), (248953283, 1)] : List FactorBlock).map factorBlockValue).prod) = 92795842518553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_31
      · exact prime_fortyAL_167
      · exact prime_fortyAL_248953283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92795842518553) ^ 46397921259276 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 92795842518553) ^ 30931947506184 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 92795842518553) ^ 2993414274792 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 92795842518553) ^ 555663727656 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 92795842518553) ^ 372744 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_101351645184883 : Nat.Prime 101351645184883 := by
  apply lucas_primality 101351645184883 (2 : ZMod 101351645184883)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (1109, 1), (183514301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (1109, 1), (183514301, 1)] : List FactorBlock).map factorBlockValue).prod) = 101351645184883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_83
      · exact prime_fortyAL_1109
      · exact prime_fortyAL_183514301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101351645184883) ^ 50675822592441 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 33783881728294 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 1221104158854 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 91390121898 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 552282 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_138114939280471 : Nat.Prime 138114939280471 := by
  apply lucas_primality 138114939280471 (6 : ZMod 138114939280471)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4603831309349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4603831309349, 1)] : List FactorBlock).map factorBlockValue).prod) = 138114939280471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_4603831309349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 138114939280471) ^ 69057469640235 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 138114939280471) ^ 46038313093490 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 138114939280471) ^ 27622987856094 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 138114939280471) ^ 30 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_138616851326671 : Nat.Prime 138616851326671 := by
  apply lucas_primality 138616851326671 (3 : ZMod 138616851326671)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (501037, 1), (3073999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (501037, 1), (3073999, 1)] : List FactorBlock).map factorBlockValue).prod) = 138616851326671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_501037
      · exact prime_fortyAL_3073999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138616851326671) ^ 69308425663335 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 46205617108890 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 27723370265334 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 276659910 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 45093330 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_158796207522221 : Nat.Prime 158796207522221 := by
  apply lucas_primality 158796207522221 (2 : ZMod 158796207522221)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) = 158796207522221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_17
      · exact prime_fortyAL_14431
      · exact prime_fortyAL_32364193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158796207522221) ^ 79398103761110 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 31759241504444 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 9340953383660 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 11003825620 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 4906540 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_1163
      · exact prime_fortyAL_1663
      · exact prime_fortyAL_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_292927119839593 : Nat.Prime 292927119839593 := by
  apply lucas_primality 292927119839593 (5 : ZMod 292927119839593)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1743613808569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1743613808569, 1)] : List FactorBlock).map factorBlockValue).prod) = 292927119839593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_1743613808569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 292927119839593) ^ 146463559919796 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 292927119839593) ^ 97642373279864 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 292927119839593) ^ 41846731405656 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 292927119839593) ^ 168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_296123742126743 : Nat.Prime 296123742126743 := by
  apply lucas_primality 296123742126743 (5 : ZMod 296123742126743)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) = 296123742126743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_31
      · exact prime_fortyAL_269
      · exact prime_fortyAL_17755350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296123742126743) ^ 148061871063371 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 9552378778282 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 1100831755118 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 16678 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_386519565736481 : Nat.Prime 386519565736481 := by
  apply lucas_primality 386519565736481 (3 : ZMod 386519565736481)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) = 386519565736481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_219613389623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 386519565736481) ^ 193259782868240 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 77303913147296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 35138142339680 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 1760 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_405406580739533 : Nat.Prime 405406580739533 := by
  apply lucas_primality 405406580739533 (2 : ZMod 405406580739533)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101351645184883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101351645184883, 1)] : List FactorBlock).map factorBlockValue).prod) = 405406580739533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_101351645184883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 405406580739533) ^ 202703290369766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 405406580739533) ^ 4 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_416726749916363 : Nat.Prime 416726749916363 := by
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_4787
      · exact prime_fortyAL_8839
      · exact prime_fortyAL_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416726749916363) ^ 208363374958181 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 87053843726 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 47146368358 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 84624586 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_471423780705089 : Nat.Prime 471423780705089 := by
  apply lucas_primality 471423780705089 (3 : ZMod 471423780705089)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (463291, 1), (15899287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (463291, 1), (15899287, 1)] : List FactorBlock).map factorBlockValue).prod) = 471423780705089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_463291
      · exact prime_fortyAL_15899287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 471423780705089) ^ 235711890352544 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 471423780705089) ^ 1017554368 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 471423780705089) ^ 29650624 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_527620858239613 : Nat.Prime 527620858239613 := by
  apply lucas_primality 527620858239613 (2 : ZMod 527620858239613)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2633, 1), (16698976397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2633, 1), (16698976397, 1)] : List FactorBlock).map factorBlockValue).prod) = 527620858239613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_2633
      · exact prime_fortyAL_16698976397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 527620858239613) ^ 263810429119806 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 527620858239613) ^ 175873619413204 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 527620858239613) ^ 200387716764 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 527620858239613) ^ 31596 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_800438006259989 : Nat.Prime 800438006259989 := by
  apply lucas_primality 800438006259989 (2 : ZMod 800438006259989)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14401, 1), (61553, 1), (225749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14401, 1), (61553, 1), (225749, 1)] : List FactorBlock).map factorBlockValue).prod) = 800438006259989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_14401
      · exact prime_fortyAL_61553
      · exact prime_fortyAL_225749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 800438006259989) ^ 400219003129994 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 55582112788 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 13004045396 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 3545699012 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1276216592026469 : Nat.Prime 1276216592026469 := by
  apply lucas_primality 1276216592026469 (2 : ZMod 1276216592026469)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276216592026469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_293081
      · exact prime_fortyAL_1088621057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1276216592026469) ^ 638108296013234 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 4354484228 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 1172324 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1388257266599051 : Nat.Prime 1388257266599051 := by
  apply lucas_primality 1388257266599051 (2 : ZMod 1388257266599051)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (352409, 1), (78786709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (352409, 1), (78786709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1388257266599051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_352409
      · exact prime_fortyAL_78786709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1388257266599051) ^ 694128633299525 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 277651453319810 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 3939335450 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 17620450 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1397726399797691 : Nat.Prime 1397726399797691 := by
  apply lucas_primality 1397726399797691 (2 : ZMod 1397726399797691)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (396107, 1), (4833779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (396107, 1), (4833779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1397726399797691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_73
      · exact prime_fortyAL_396107
      · exact prime_fortyAL_4833779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1397726399797691) ^ 698863199898845 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397726399797691) ^ 279545279959538 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397726399797691) ^ 19146936983530 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397726399797691) ^ 3528658670 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397726399797691) ^ 289158110 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_41
      · exact prime_fortyAL_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2065202483007581 : Nat.Prime 2065202483007581 := by
  apply lucas_primality 2065202483007581 (3 : ZMod 2065202483007581)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (14751446307197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (14751446307197, 1)] : List FactorBlock).map factorBlockValue).prod) = 2065202483007581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_14751446307197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2065202483007581) ^ 1032601241503790 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 413040496601516 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 295028926143940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 140 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2509579760732741 : Nat.Prime 2509579760732741 := by
  apply lucas_primality 2509579760732741 (2 : ZMod 2509579760732741)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (571, 1), (2917, 1), (75335291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (571, 1), (2917, 1), (75335291, 1)] : List FactorBlock).map factorBlockValue).prod) = 2509579760732741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_571
      · exact prime_fortyAL_2917
      · exact prime_fortyAL_75335291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2509579760732741) ^ 1254789880366370 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2509579760732741) ^ 501915952146548 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2509579760732741) ^ 4395060876940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2509579760732741) ^ 860329023220 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2509579760732741) ^ 33312140 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2550639502217021 : Nat.Prime 2550639502217021 := by
  apply lucas_primality 2550639502217021 (2 : ZMod 2550639502217021)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (463, 1), (1873, 1), (147061949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (463, 1), (1873, 1), (147061949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2550639502217021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_463
      · exact prime_fortyAL_1873
      · exact prime_fortyAL_147061949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2550639502217021) ^ 1275319751108510 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2550639502217021) ^ 510127900443404 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2550639502217021) ^ 5508940609540 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2550639502217021) ^ 1361793647740 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 2550639502217021) ^ 17343980 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2778766659246041 : Nat.Prime 2778766659246041 := by
  apply lucas_primality 2778766659246041 (11 : ZMod 2778766659246041)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (69469166481151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (69469166481151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2778766659246041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_69469166481151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2778766659246041) ^ 1389383329623020 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 2778766659246041) ^ 555753331849208 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (11 : ZMod 2778766659246041) ^ 40 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2820880298726107 : Nat.Prime 2820880298726107 := by
  apply lucas_primality 2820880298726107 (3 : ZMod 2820880298726107)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820880298726107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_317
      · exact prime_fortyAL_1483112670203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2820880298726107) ^ 1410440149363053 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 940293432908702 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 8898676021218 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 1902 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2974149575688209 : Nat.Prime 2974149575688209 := by
  apply lucas_primality 2974149575688209 (3 : ZMod 2974149575688209)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (5996269305823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (5996269305823, 1)] : List FactorBlock).map factorBlockValue).prod) = 2974149575688209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_31
      · exact prime_fortyAL_5996269305823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2974149575688209) ^ 1487074787844104 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2974149575688209) ^ 95940308893168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 2974149575688209) ^ 496 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5523140549247743 : Nat.Prime 5523140549247743 := by
  apply lucas_primality 5523140549247743 (5 : ZMod 5523140549247743)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523140549247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_31
      · exact prime_fortyAL_101
      · exact prime_fortyAL_463
      · exact prime_fortyAL_631
      · exact prime_fortyAL_97387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5523140549247743) ^ 2761570274623871 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 178165824169282 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 54684559893542 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 11929029264034 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 8752996116082 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 56713324666 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7339230765449701 : Nat.Prime 7339230765449701 := by
  apply lucas_primality 7339230765449701 (6 : ZMod 7339230765449701)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (71, 1), (199, 1), (587, 1), (226901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (71, 1), (199, 1), (587, 1), (226901, 1)] : List FactorBlock).map factorBlockValue).prod) = 7339230765449701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_13
      · exact prime_fortyAL_71
      · exact prime_fortyAL_199
      · exact prime_fortyAL_587
      · exact prime_fortyAL_226901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7339230765449701) ^ 3669615382724850 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 2446410255149900 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 1467846153089940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 564556212726900 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 103369447400700 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 36880556610300 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 12502948493100 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 7339230765449701) ^ 32345519700 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_8382546608565221 : Nat.Prime 8382546608565221 := by
  apply lucas_primality 8382546608565221 (2 : ZMod 8382546608565221)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (4605794839871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (4605794839871, 1)] : List FactorBlock).map factorBlockValue).prod) = 8382546608565221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_13
      · exact prime_fortyAL_4605794839871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8382546608565221) ^ 4191273304282610 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 8382546608565221) ^ 1676509321713044 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 8382546608565221) ^ 1197506658366460 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 8382546608565221) ^ 644811277581940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 8382546608565221) ^ 1820 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_9691183070205617 : Nat.Prime 9691183070205617 := by
  apply lucas_primality 9691183070205617 (3 : ZMod 9691183070205617)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) = 9691183070205617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_12251
      · exact prime_fortyAL_7062967943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9691183070205617) ^ 4845591535102808 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1384454724315088 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 791052409616 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1372112 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_9899266128252901 : Nat.Prime 9899266128252901 := by
  apply lucas_primality 9899266128252901 (10 : ZMod 9899266128252901)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 2), (367, 1), (719, 1), (2552059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 2), (367, 1), (719, 1), (2552059, 1)] : List FactorBlock).map factorBlockValue).prod) = 9899266128252901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_367
      · exact prime_fortyAL_719
      · exact prime_fortyAL_2552059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9899266128252901) ^ 4949633064126450 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 3299755376084300 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 1979853225650580 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 1414180875464700 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 26973477188700 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 13768103099100 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 9899266128252901) ^ 3878933100 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_10950386820164879 : Nat.Prime 10950386820164879 := by
  apply lucas_primality 10950386820164879 (17 : ZMod 10950386820164879)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) = 10950386820164879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3586771
      · exact prime_fortyAL_1526496509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 10950386820164879) ^ 5475193410082439 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 3052993018 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 7173542 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_384973
      · exact prime_fortyAL_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_19
      · exact prime_fortyAL_656951
      · exact prime_fortyAL_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_28583317353999781 : Nat.Prime 28583317353999781 := by
  apply lucas_primality 28583317353999781 (2 : ZMod 28583317353999781)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) = 28583317353999781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_158796207522221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28583317353999781) ^ 14291658676999890 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 9527772451333260 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 5716663470799956 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_44419272177508427 : Nat.Prime 44419272177508427 := by
  apply lucas_primality 44419272177508427 (2 : ZMod 44419272177508427)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (181, 1), (2351, 1), (4744796093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (181, 1), (2351, 1), (4744796093, 1)] : List FactorBlock).map factorBlockValue).prod) = 44419272177508427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_181
      · exact prime_fortyAL_2351
      · exact prime_fortyAL_4744796093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44419272177508427) ^ 22209636088754213 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 44419272177508427) ^ 4038115652500766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 44419272177508427) ^ 245410343522146 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 44419272177508427) ^ 18893778042326 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 44419272177508427) ^ 9361682 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_53513668657618357 : Nat.Prime 53513668657618357 := by
  apply lucas_primality 53513668657618357 (2 : ZMod 53513668657618357)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (405406580739533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (405406580739533, 1)] : List FactorBlock).map factorBlockValue).prod) = 53513668657618357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_405406580739533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53513668657618357) ^ 26756834328809178 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 17837889552539452 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 4864878968874396 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 132 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_17
      · exact prime_fortyAL_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_85512338798115589 : Nat.Prime 85512338798115589 := by
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_59
      · exact prime_fortyAL_71
      · exact prime_fortyAL_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85512338798115589) ^ 42756169399057794 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 28504112932705196 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1449361674544332 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1204399138001628 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 3569028 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_272206049047378717 : Nat.Prime 272206049047378717 := by
  apply lucas_primality 272206049047378717 (2 : ZMod 272206049047378717)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (131, 1), (6067, 1), (1678890277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (131, 1), (6067, 1), (1678890277, 1)] : List FactorBlock).map factorBlockValue).prod) = 272206049047378717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_17
      · exact prime_fortyAL_131
      · exact prime_fortyAL_6067
      · exact prime_fortyAL_1678890277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 272206049047378717) ^ 136103024523689358 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 272206049047378717) ^ 90735349682459572 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 272206049047378717) ^ 16012120532198748 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 272206049047378717) ^ 2077908771354036 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 272206049047378717) ^ 44866663762548 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 272206049047378717) ^ 162134508 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_29
      · exact prime_fortyAL_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_505184984920871293 : Nat.Prime 505184984920871293 := by
  apply lucas_primality 505184984920871293 (2 : ZMod 505184984920871293)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (991, 1), (1464864774119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (991, 1), (1464864774119, 1)] : List FactorBlock).map factorBlockValue).prod) = 505184984920871293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_29
      · exact prime_fortyAL_991
      · exact prime_fortyAL_1464864774119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 505184984920871293) ^ 252592492460435646 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 505184984920871293) ^ 168394994973623764 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 505184984920871293) ^ 17420171893823148 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 505184984920871293) ^ 509772941393412 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 505184984920871293) ^ 344868 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_61717
      · exact prime_fortyAL_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1249558476287426663 : Nat.Prime 1249558476287426663 := by
  apply lucas_primality 1249558476287426663 (5 : ZMod 1249558476287426663)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249558476287426663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_874459
      · exact prime_fortyAL_102067880687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1249558476287426663) ^ 624779238143713331 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 178508353755346666 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 1428950329618 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 12242426 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1290687866434579649 : Nat.Prime 1290687866434579649 := by
  apply lucas_primality 1290687866434579649 (3 : ZMod 1290687866434579649)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (47, 1), (541, 1), (113304743063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (47, 1), (541, 1), (113304743063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1290687866434579649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_47
      · exact prime_fortyAL_541
      · exact prime_fortyAL_113304743063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1290687866434579649) ^ 645343933217289824 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1290687866434579649) ^ 184383980919225664 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1290687866434579649) ^ 27461443966693184 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1290687866434579649) ^ 2385744669934528 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 1290687866434579649) ^ 11391296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2499116952574853327 : Nat.Prime 2499116952574853327 := by
  apply lucas_primality 2499116952574853327 (5 : ZMod 2499116952574853327)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2499116952574853327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_1249558476287426663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2499116952574853327) ^ 1249558476287426663 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 2499116952574853327) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_3826002797968790539 : Nat.Prime 3826002797968790539 := by
  apply lucas_primality 3826002797968790539 (7 : ZMod 3826002797968790539)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1201, 1), (1198103, 1), (13428977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1201, 1), (1198103, 1), (13428977, 1)] : List FactorBlock).map factorBlockValue).prod) = 3826002797968790539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_1201
      · exact prime_fortyAL_1198103
      · exact prime_fortyAL_13428977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3826002797968790539) ^ 1913001398984395269 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 3826002797968790539) ^ 1275334265989596846 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 3826002797968790539) ^ 347818436178980958 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 3826002797968790539) ^ 3185680930864938 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 3826002797968790539) ^ 3193383872646 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 3826002797968790539) ^ 284906497194 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4566860651326217533 : Nat.Prime 4566860651326217533 := by
  apply lucas_primality 4566860651326217533 (2 : ZMod 4566860651326217533)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (26619991, 1), (14296463171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (26619991, 1), (14296463171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4566860651326217533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_26619991
      · exact prime_fortyAL_14296463171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4566860651326217533) ^ 2283430325663108766 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4566860651326217533) ^ 1522286883775405844 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4566860651326217533) ^ 171557558052 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4566860651326217533) ^ 319439892 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_439
      · exact prime_fortyAL_853
      · exact prime_fortyAL_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_10486662089795850443 : Nat.Prime 10486662089795850443 := by
  apply lucas_primality 10486662089795850443 (2 : ZMod 10486662089795850443)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (971, 1), (25733, 1), (178287611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (971, 1), (25733, 1), (178287611, 1)] : List FactorBlock).map factorBlockValue).prod) = 10486662089795850443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_107
      · exact prime_fortyAL_971
      · exact prime_fortyAL_25733
      · exact prime_fortyAL_178287611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10486662089795850443) ^ 5243331044897925221 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 10486662089795850443) ^ 953332917254168222 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 10486662089795850443) ^ 98006187755101406 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 10486662089795850443) ^ 10799857970953502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 10486662089795850443) ^ 407518054241474 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 10486662089795850443) ^ 58818793022 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11184114340779081913 : Nat.Prime 11184114340779081913 := by
  apply lucas_primality 11184114340779081913 (5 : ZMod 11184114340779081913)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (23, 1), (47, 1), (8581, 1), (19381, 1), (123433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (23, 1), (47, 1), (8581, 1), (19381, 1), (123433, 1)] : List FactorBlock).map factorBlockValue).prod) = 11184114340779081913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_23
      · exact prime_fortyAL_47
      · exact prime_fortyAL_8581
      · exact prime_fortyAL_19381
      · exact prime_fortyAL_123433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11184114340779081913) ^ 5592057170389540956 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 3728038113593027304 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 1597730620111297416 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 486265840903438344 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 237959879591044296 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 1303357923409752 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 577065906856152 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11184114340779081913) ^ 90608786473464 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_13451362101445396397 : Nat.Prime 13451362101445396397 := by
  apply lucas_primality 13451362101445396397 (2 : ZMod 13451362101445396397)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) = 13451362101445396397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_347
      · exact prime_fortyAL_9691183070205617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13451362101445396397) ^ 6725681050722698198 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 38764732280822468 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 1388 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_19506602764358177057 : Nat.Prime 19506602764358177057 := by
  apply lucas_primality 19506602764358177057 (3 : ZMod 19506602764358177057)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2081, 1), (292927119839593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2081, 1), (292927119839593, 1)] : List FactorBlock).map factorBlockValue).prod) = 19506602764358177057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_2081
      · exact prime_fortyAL_292927119839593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19506602764358177057) ^ 9753301382179088528 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 19506602764358177057) ^ 9373667834866976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 19506602764358177057) ^ 66592 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_34920059982009677359 : Nat.Prime 34920059982009677359 := by
  apply lucas_primality 34920059982009677359 (3 : ZMod 34920059982009677359)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (61, 1), (7339230765449701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (61, 1), (7339230765449701, 1)] : List FactorBlock).map factorBlockValue).prod) = 34920059982009677359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_13
      · exact prime_fortyAL_61
      · exact prime_fortyAL_7339230765449701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34920059982009677359) ^ 17460029991004838679 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920059982009677359) ^ 11640019994003225786 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920059982009677359) ^ 2686158460154590566 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920059982009677359) ^ 572459999705076678 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 34920059982009677359) ^ 4758 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_35827783237643689169 : Nat.Prime 35827783237643689169 := by
  apply lucas_primality 35827783237643689169 (3 : ZMod 35827783237643689169)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (410497, 1), (5454939871309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (410497, 1), (5454939871309, 1)] : List FactorBlock).map factorBlockValue).prod) = 35827783237643689169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_410497
      · exact prime_fortyAL_5454939871309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35827783237643689169) ^ 17913891618821844584 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 35827783237643689169) ^ 87279037940944 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 35827783237643689169) ^ 6567952 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_36084410004208516523 : Nat.Prime 36084410004208516523 := by
  apply lucas_primality 36084410004208516523 (2 : ZMod 36084410004208516523)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (17, 1), (233, 1), (1836511, 1), (17344237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (17, 1), (233, 1), (1836511, 1), (17344237, 1)] : List FactorBlock).map factorBlockValue).prod) = 36084410004208516523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_233
      · exact prime_fortyAL_1836511
      · exact prime_fortyAL_17344237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36084410004208516523) ^ 18042205002104258261 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 3280400909473501502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 2775723846477578194 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 2122612353188736266 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 154868712464414234 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 19648349508502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 36084410004208516523) ^ 2080484140306 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_65674048039713268091 : Nat.Prime 65674048039713268091 := by
  apply lucas_primality 65674048039713268091 (2 : ZMod 65674048039713268091)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (505184984920871293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (505184984920871293, 1)] : List FactorBlock).map factorBlockValue).prod) = 65674048039713268091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_13
      · exact prime_fortyAL_505184984920871293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65674048039713268091) ^ 32837024019856634045 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 65674048039713268091) ^ 13134809607942653618 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 65674048039713268091) ^ 5051849849208712930 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 65674048039713268091) ^ 130 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_77941279325171544881 : Nat.Prime 77941279325171544881 := by
  apply lucas_primality 77941279325171544881 (3 : ZMod 77941279325171544881)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (304067, 1), (246470474641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (304067, 1), (246470474641, 1)] : List FactorBlock).map factorBlockValue).prod) = 77941279325171544881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_13
      · exact prime_fortyAL_304067
      · exact prime_fortyAL_246470474641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 77941279325171544881) ^ 38970639662585772440 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 77941279325171544881) ^ 15588255865034308976 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 77941279325171544881) ^ 5995483025013195760 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 77941279325171544881) ^ 256329293626640 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 77941279325171544881) ^ 316229680 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_138564817290563326591 : Nat.Prime 138564817290563326591 := by
  apply lucas_primality 138564817290563326591 (3 : ZMod 138564817290563326591)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (383, 1), (1429, 1), (366921263173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (383, 1), (1429, 1), (366921263173, 1)] : List FactorBlock).map factorBlockValue).prod) = 138564817290563326591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_23
      · exact prime_fortyAL_383
      · exact prime_fortyAL_1429
      · exact prime_fortyAL_366921263173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138564817290563326591) ^ 69282408645281663295 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 46188272430187775530 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 27712963458112665318 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 6024557273502753330 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 361788034701209730 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 96966282218728710 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 377641830 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_522739262784491482721 : Nat.Prime 522739262784491482721 := by
  apply lucas_primality 522739262784491482721 (6 : ZMod 522739262784491482721)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (439, 1), (7867, 1), (946000722259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (439, 1), (7867, 1), (946000722259, 1)] : List FactorBlock).map factorBlockValue).prod) = 522739262784491482721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_439
      · exact prime_fortyAL_7867
      · exact prime_fortyAL_946000722259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522739262784491482721) ^ 261369631392245741360 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 522739262784491482721) ^ 104547852556898296544 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 522739262784491482721) ^ 1190750029121848480 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 522739262784491482721) ^ 66447090731472160 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 522739262784491482721) ^ 552578080 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_542088903902523452581 : Nat.Prime 542088903902523452581 := by
  apply lucas_primality 542088903902523452581 (6 : ZMod 542088903902523452581)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (1290687866434579649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (1290687866434579649, 1)] : List FactorBlock).map factorBlockValue).prod) = 542088903902523452581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_1290687866434579649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 542088903902523452581) ^ 271044451951261726290 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 542088903902523452581) ^ 180696301300841150860 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 542088903902523452581) ^ 108417780780504690516 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 542088903902523452581) ^ 77441271986074778940 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (6 : ZMod 542088903902523452581) ^ 420 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_651661281419424648499 : Nat.Prime 651661281419424648499 := by
  apply lucas_primality 651661281419424648499 (2 : ZMod 651661281419424648499)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (272206049047378717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (272206049047378717, 1)] : List FactorBlock).map factorBlockValue).prod) = 651661281419424648499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_7
      · exact prime_fortyAL_19
      · exact prime_fortyAL_272206049047378717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 651661281419424648499) ^ 325830640709712324249 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 651661281419424648499) ^ 217220427139808216166 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 651661281419424648499) ^ 93094468774203521214 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 651661281419424648499) ^ 34297962179969718342 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 651661281419424648499) ^ 2394 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_766661019018383304097 : Nat.Prime 766661019018383304097 := by
  apply lucas_primality 766661019018383304097 (5 : ZMod 766661019018383304097)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (31, 1), (101, 1), (2550639502217021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (31, 1), (101, 1), (2550639502217021, 1)] : List FactorBlock).map factorBlockValue).prod) = 766661019018383304097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_31
      · exact prime_fortyAL_101
      · exact prime_fortyAL_2550639502217021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 766661019018383304097) ^ 383330509509191652048 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 766661019018383304097) ^ 255553673006127768032 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 766661019018383304097) ^ 24731000613496235616 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 766661019018383304097) ^ 7590703158597854496 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 766661019018383304097) ^ 300576 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1203321123045496636931 : Nat.Prime 1203321123045496636931 := by
  apply lucas_primality 1203321123045496636931 (2 : ZMod 1203321123045496636931)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (359, 1), (116329, 1), (7766497153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (359, 1), (116329, 1), (7766497153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1203321123045496636931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_53
      · exact prime_fortyAL_359
      · exact prime_fortyAL_116329
      · exact prime_fortyAL_7766497153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1203321123045496636931) ^ 601660561522748318465 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 240664224609099327386 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 171903017577928090990 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 22704172132933898810 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 3351869423525060270 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 10344119893109170 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203321123045496636931) ^ 154937431810 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2020562502386822800799 : Nat.Prime 2020562502386822800799 := by
  apply lucas_primality 2020562502386822800799 (7 : ZMod 2020562502386822800799)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1423, 1), (2801, 1), (36209809875559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1423, 1), (2801, 1), (36209809875559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020562502386822800799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_7
      · exact prime_fortyAL_1423
      · exact prime_fortyAL_2801
      · exact prime_fortyAL_36209809875559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2020562502386822800799) ^ 1010281251193411400399 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 288651786055260400114 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 1419931484460170626 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 721371832340886398 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 55801522 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_19
      · exact prime_fortyAL_107
      · exact prime_fortyAL_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4041125004773645601599 : Nat.Prime 4041125004773645601599 := by
  apply lucas_primality 4041125004773645601599 (13 : ZMod 4041125004773645601599)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2020562502386822800799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2020562502386822800799, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041125004773645601599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_2020562502386822800799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 4041125004773645601599) ^ 2020562502386822800799 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (13 : ZMod 4041125004773645601599) ^ 2 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_5221767975959770844009 : Nat.Prime 5221767975959770844009 := by
  apply lucas_primality 5221767975959770844009 (3 : ZMod 5221767975959770844009)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (7746119, 1), (946789455011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (7746119, 1), (946789455011, 1)] : List FactorBlock).map factorBlockValue).prod) = 5221767975959770844009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_89
      · exact prime_fortyAL_7746119
      · exact prime_fortyAL_946789455011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5221767975959770844009) ^ 2610883987979885422004 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5221767975959770844009) ^ 58671550291682818472 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5221767975959770844009) ^ 674114091967832 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 5221767975959770844009) ^ 5515236728 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_6891984566505300835487 : Nat.Prime 6891984566505300835487 := by
  apply lucas_primality 6891984566505300835487 (5 : ZMod 6891984566505300835487)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6891984566505300835487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_11637001
      · exact prime_fortyAL_296123742126743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6891984566505300835487) ^ 3445992283252650417743 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 592247484253486 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 23274002 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_7897952918603962932167 : Nat.Prime 7897952918603962932167 := by
  apply lucas_primality 7897952918603962932167 (5 : ZMod 7897952918603962932167)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (379, 1), (397153, 1), (200270135539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (379, 1), (397153, 1), (200270135539, 1)] : List FactorBlock).map factorBlockValue).prod) = 7897952918603962932167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_131
      · exact prime_fortyAL_379
      · exact prime_fortyAL_397153
      · exact prime_fortyAL_200270135539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7897952918603962932167) ^ 3948976459301981466083 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7897952918603962932167) ^ 60289716935908113986 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7897952918603962932167) ^ 20838925906606762354 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7897952918603962932167) ^ 19886423918751622 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 7897952918603962932167) ^ 39436498594 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_10084938184863487564601 : Nat.Prime 10084938184863487564601 := by
  apply lucas_primality 10084938184863487564601 (3 : ZMod 10084938184863487564601)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (97, 1), (50101, 1), (119557, 1), (86786087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (97, 1), (50101, 1), (119557, 1), (86786087, 1)] : List FactorBlock).map factorBlockValue).prod) = 10084938184863487564601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_5
      · exact prime_fortyAL_97
      · exact prime_fortyAL_50101
      · exact prime_fortyAL_119557
      · exact prime_fortyAL_86786087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10084938184863487564601) ^ 5042469092431743782300 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 2016987636972697512920 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 103968434895499871800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 201292153547104600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 84352553048867800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 116204549985800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_29
      · exact prime_fortyAL_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_19647584683708272101017 : Nat.Prime 19647584683708272101017 := by
  apply lucas_primality 19647584683708272101017 (5 : ZMod 19647584683708272101017)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (103, 1), (596369, 1), (13327406448887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (103, 1), (596369, 1), (13327406448887, 1)] : List FactorBlock).map factorBlockValue).prod) = 19647584683708272101017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_103
      · exact prime_fortyAL_596369
      · exact prime_fortyAL_13327406448887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19647584683708272101017) ^ 9823792341854136050508 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 6549194894569424033672 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 190753249356390991272 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 32945348741648664 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 1474224168 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_26405844248568130572469 : Nat.Prime 26405844248568130572469 := by
  apply lucas_primality 26405844248568130572469 (2 : ZMod 26405844248568130572469)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (67261, 1), (2974149575688209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (67261, 1), (2974149575688209, 1)] : List FactorBlock).map factorBlockValue).prod) = 26405844248568130572469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_11
      · exact prime_fortyAL_67261
      · exact prime_fortyAL_2974149575688209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26405844248568130572469) ^ 13202922124284065286234 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 26405844248568130572469) ^ 8801948082856043524156 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 26405844248568130572469) ^ 2400531295324375506588 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 26405844248568130572469) ^ 392587743990843588 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 26405844248568130572469) ^ 8878452 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_325064272063794520937129 : Nat.Prime 325064272063794520937129 := by
  apply lucas_primality 325064272063794520937129 (3 : ZMod 325064272063794520937129)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (766661019018383304097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (766661019018383304097, 1)] : List FactorBlock).map factorBlockValue).prod) = 325064272063794520937129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_53
      · exact prime_fortyAL_766661019018383304097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 325064272063794520937129) ^ 162532136031897260468564 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 325064272063794520937129) ^ 6133288152147066432776 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (3 : ZMod 325064272063794520937129) ^ 424 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_463261646167912959194123 : Nat.Prime 463261646167912959194123 := by
  apply lucas_primality 463261646167912959194123 (2 : ZMod 463261646167912959194123)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (242989, 1), (18337103, 1), (115779767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (242989, 1), (18337103, 1), (115779767, 1)] : List FactorBlock).map factorBlockValue).prod) = 463261646167912959194123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_449
      · exact prime_fortyAL_242989
      · exact prime_fortyAL_18337103
      · exact prime_fortyAL_115779767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 463261646167912959194123) ^ 231630823083956479597061 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 1031763131777088995978 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 1906512830489910898 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 25263622403599574 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 4001231460138566 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_3061
      · exact prime_fortyAL_61379
      · exact prime_fortyAL_382747
      · exact prime_fortyAL_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4141765227195033342131237 : Nat.Prime 4141765227195033342131237 := by
  apply lucas_primality 4141765227195033342131237 (2 : ZMod 4141765227195033342131237)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (30083567, 1), (800438006259989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (30083567, 1), (800438006259989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4141765227195033342131237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_43
      · exact prime_fortyAL_30083567
      · exact prime_fortyAL_800438006259989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4141765227195033342131237) ^ 2070882613597516671065618 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 96320121562675194003052 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 137675337076718108 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 5174373524 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4362206010895018051882157 : Nat.Prime 4362206010895018051882157 := by
  apply lucas_primality 4362206010895018051882157 (2 : ZMod 4362206010895018051882157)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (109, 1), (2633, 1), (5119, 1), (8340530738857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (109, 1), (2633, 1), (5119, 1), (8340530738857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4362206010895018051882157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_89
      · exact prime_fortyAL_109
      · exact prime_fortyAL_2633
      · exact prime_fortyAL_5119
      · exact prime_fortyAL_8340530738857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4362206010895018051882157) ^ 2181103005447509025941078 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362206010895018051882157) ^ 49013550684213685976204 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362206010895018051882157) ^ 40020238632064385797084 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362206010895018051882157) ^ 1656743642573117376332 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362206010895018051882157) ^ 852159798963668304724 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362206010895018051882157) ^ 523013000908 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_4371076380821969747708149 : Nat.Prime 4371076380821969747708149 := by
  apply lucas_primality 4371076380821969747708149 (2 : ZMod 4371076380821969747708149)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (79, 1), (274991737, 1), (578179136237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (79, 1), (274991737, 1), (578179136237, 1)] : List FactorBlock).map factorBlockValue).prod) = 4371076380821969747708149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_29
      · exact prime_fortyAL_79
      · exact prime_fortyAL_274991737
      · exact prime_fortyAL_578179136237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4371076380821969747708149) ^ 2185538190410984873854074 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4371076380821969747708149) ^ 1457025460273989915902716 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4371076380821969747708149) ^ 150726771752481715438212 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4371076380821969747708149) ^ 55330080769898351236812 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4371076380821969747708149) ^ 15895300813427604 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 4371076380821969747708149) ^ 7560072833604 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_11731747795612227908820259 : Nat.Prime 11731747795612227908820259 := by
  apply lucas_primality 11731747795612227908820259 (2 : ZMod 11731747795612227908820259)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1013, 1), (904369, 1), (92795842518553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1013, 1), (904369, 1), (92795842518553, 1)] : List FactorBlock).map factorBlockValue).prod) = 11731747795612227908820259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_23
      · exact prime_fortyAL_1013
      · exact prime_fortyAL_904369
      · exact prime_fortyAL_92795842518553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11731747795612227908820259) ^ 5865873897806113954410129 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11731747795612227908820259) ^ 3910582598537409302940086 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11731747795612227908820259) ^ 510075991113575126470446 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11731747795612227908820259) ^ 11581192295767253611866 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11731747795612227908820259) ^ 12972302009038598082 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 11731747795612227908820259) ^ 126425359986 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_12709130707904566165131541 : Nat.Prime 12709130707904566165131541 := by
  apply lucas_primality 12709130707904566165131541 (2 : ZMod 12709130707904566165131541)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5330309, 1), (64381453, 1), (617236267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5330309, 1), (64381453, 1), (617236267, 1)] : List FactorBlock).map factorBlockValue).prod) = 12709130707904566165131541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_5330309
      · exact prime_fortyAL_64381453
      · exact prime_fortyAL_617236267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12709130707904566165131541) ^ 6354565353952283082565770 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 12709130707904566165131541) ^ 4236376902634855388377180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 12709130707904566165131541) ^ 2541826141580913233026308 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 12709130707904566165131541) ^ 2384314062825357060 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 12709130707904566165131541) ^ 197403601746990180 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (2 : ZMod 12709130707904566165131541) ^ 20590382301538620 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_482557911878702966331168001 : Nat.Prime 482557911878702966331168001 := by
  apply lucas_primality 482557911878702966331168001 (7 : ZMod 482557911878702966331168001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 482557911878702966331168001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 482557911878702966331168001) ^ 241278955939351483165584000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 160852637292900988777056000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 96511582375740593266233600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 43868901079882087848288000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 37119839375284843563936000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 28385759522276645078304000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 25397784835721208754272000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 20980778777334911579616000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 16639927995817343666592000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 15566384254151708591328000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 13042105726451431522464000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 11769705167773243081248000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 11222277020434952705376000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 10267189614440488645344000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 9104866261862320119456000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 8178947658961067225952000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 7910785440634474857888000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_503092291107583943621856001 : Nat.Prime 503092291107583943621856001 := by
  apply lucas_primality 503092291107583943621856001 (73 : ZMod 503092291107583943621856001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 503092291107583943621856001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 503092291107583943621856001) ^ 251546145553791971810928000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 167697430369194647873952000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 100618458221516788724371200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 71870327301083420517408000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 45735662827962176692896000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 38699407008275687970912000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 29593664182799055507168000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 26478541637241260190624000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 21873577874242780157472000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 17348010038192549780064000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 16228783584115611084576000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 13597088948853620097888000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 12270543685550827893216000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 11699820723432184735392000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 9492307379388376294752000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 8526987984874304129184000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 8247414608321048256096000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_606290709796319111544288001 : Nat.Prime 606290709796319111544288001 := by
  apply lucas_primality 606290709796319111544288001 (65 : ZMod 606290709796319111544288001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 606290709796319111544288001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (65 : ZMod 606290709796319111544288001) ^ 303145354898159555772144000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 202096903265439703848096000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 121258141959263822308857600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 86612958542331301649184000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 55117337254210828322208000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 35664159399783477149664000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 31910037357701005870752000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 26360465643318222241056000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 20906576199873072811872000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 19557764832139326178848000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 16386235399900516528224000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 14787578287715100281568000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 14099783948751607245216000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 12899802336091895990304000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 11439447354647530406496000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 10276113725361340873632000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 9939191963874083795808000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_750645640700204614292928001 : Nat.Prime 750645640700204614292928001 := by
  apply lucas_primality 750645640700204614292928001 (107 : ZMod 750645640700204614292928001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 750645640700204614292928001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 750645640700204614292928001) ^ 375322820350102307146464000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 250215213566734871430976000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 150129128140040922858585600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 107235091528600659184704000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 68240512790927692208448000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 57741972361554201099456000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 44155625923541447899584000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 39507665300010769173312000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 32636766986965418012736000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 25884332437938090148032000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 24214375506458213364288000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 20287720018924449034944000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 18308430260980600348608000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 17456875365121037541696000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 15971183844685204559424000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 14163125296230275741376000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 12722807469494993462592000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 750645640700204614292928001) ^ 12305666240986960890048000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_815356471795049839663008001 : Nat.Prime 815356471795049839663008001 := by
  apply lucas_primality 815356471795049839663008001 (71 : ZMod 815356471795049839663008001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 815356471795049839663008001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 815356471795049839663008001) ^ 407678235897524919831504000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 271785490598349946554336000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 163071294359009967932601600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 116479495970721405666144000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 74123315617731803605728000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 62719728599619218435616000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 47962145399708814097824000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 42913498515528938929632000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 35450281382393471289696000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 26301821670808059343968000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 22036661399866211882784000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 19886743214513410723488000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 18961778413838368364256000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 17348010038192549780064000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 15384084373491506408736000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 13819601216865251519712000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 13366499537623767863328000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_892276893662507371706688001 : Nat.Prime 892276893662507371706688001 := by
  apply lucas_primality 892276893662507371706688001 (71 : ZMod 892276893662507371706688001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 892276893662507371706688001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 892276893662507371706688001) ^ 446138446831253685853344000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 297425631220835790568896000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 178455378732501474341337600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 127468127666072481672384000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 81116081242046124700608000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 68636684127885182438976000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 52486876097794551276864000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 46961941771710914300352000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 38794647550543798769856000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 30768168746983012817472000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 28783125602016366829248000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 24115591720608307343424000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 21762851064939204187968000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 20750625434011799342016000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 18984614758776752589504000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 15123337180720463927232000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (71 : ZMod 892276893662507371706688001) ^ 14627490060041104454208000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_909436064694478667316432001 : Nat.Prime 909436064694478667316432001 := by
  apply lucas_primality 909436064694478667316432001 (26 : ZMod 909436064694478667316432001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478667316432001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 909436064694478667316432001) ^ 454718032347239333658216000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 303145354898159555772144000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 181887212938895733463286400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 129919437813496952473776000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 82676005881316242483312000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 53496239099675215724496000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 47865056036551508806128000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 39540698464977333361584000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 31359864299809609217808000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 29336647248208989268272000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 24579353099850774792336000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 22181367431572650422352000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 21149675923127410867824000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 19349703504137843985456000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 17159171031971295609744000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 15414170588042011310448000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 14908787945811125693712000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1074788076457111152283056001 : Nat.Prime 1074788076457111152283056001 := by
  apply lucas_primality 1074788076457111152283056001 (67 : ZMod 1074788076457111152283056001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074788076457111152283056001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1074788076457111152283056001) ^ 537394038228555576141528000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 358262692152370384094352000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 214957615291422230456611200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 153541153779587307469008000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 82676005881316242483312000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 63222828026888891310768000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 56567793497742692225424000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 46729916367700484881872000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 37061657808865901802864000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 34670583111519714589776000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 29048326390732733845488000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 26214343328222223226416000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 24995071545514212843792000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 22867831413981088346448000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 20279020310511531175152000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 18216747058595104275984000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 17619476663231330365296000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem prime_fortyAL_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← fortyALFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyAL_2
      · exact prime_fortyAL_3
      · exact prime_fortyAL_5
      · exact prime_fortyAL_7
      · exact prime_fortyAL_11
      · exact prime_fortyAL_13
      · exact prime_fortyAL_17
      · exact prime_fortyAL_19
      · exact prime_fortyAL_23
      · exact prime_fortyAL_29
      · exact prime_fortyAL_31
      · exact prime_fortyAL_37
      · exact prime_fortyAL_41
      · exact prime_fortyAL_43
      · exact prime_fortyAL_47
      · exact prime_fortyAL_53
      · exact prime_fortyAL_59
      · exact prime_fortyAL_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← fortyALFastPow_eq_pow]
      decide

private theorem phi_fortyAL_47290675364112890700454464000 : Nat.totient 47290675364112890700454464000 = 6222854738374425575424000000 := by
  rw [← show ((([(2, 9), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_7, prime_fortyAL_11, prime_fortyAL_13, prime_fortyAL_17, prime_fortyAL_19, prime_fortyAL_23, prime_fortyAL_29, prime_fortyAL_31, prime_fortyAL_37, prime_fortyAL_41, prime_fortyAL_43, prime_fortyAL_47, prime_fortyAL_53, prime_fortyAL_59, prime_fortyAL_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464001 : Nat.totient 47290675364112890700454464001 = 47290495845782189725895116800 := by
  rw [← show ((([(267373, 1), (17867137, 1), (9899266128252901, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_267373, prime_fortyAL_17867137, prime_fortyAL_9899266128252901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464002 : Nat.totient 47290675364112890700454464002 = 23543826289993479239786926080 := by
  rw [← show ((([(2, 1), (233, 1), (806041, 1), (503705849, 1), (249951341833, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_233, prime_fortyAL_806041, prime_fortyAL_503705849, prime_fortyAL_249951341833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464003 : Nat.totient 47290675364112890700454464003 = 31515105406628331754952724480 := by
  rw [← show ((([(3, 1), (4057, 1), (7433, 1), (522739262784491482721, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_4057, prime_fortyAL_7433, prime_fortyAL_522739262784491482721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464004 : Nat.totient 47290675364112890700454464004 = 23605984450181700082453176096 := by
  rw [← show ((([(2, 2), (859, 1), (1997, 1), (6891984566505300835487, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_859, prime_fortyAL_1997, prime_fortyAL_6891984566505300835487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464005 : Nat.totient 47290675364112890700454464005 = 37591554647922312472152786432 := by
  rw [← show ((([(5, 1), (157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_157, prime_fortyAL_4315799, prime_fortyAL_7041049, prime_fortyAL_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464006 : Nat.totient 47290675364112890700454464006 = 15733417806114018982710235200 := by
  rw [← show ((([(2, 1), (3, 1), (523, 1), (10855569737, 1), (1388257266599051, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_523, prime_fortyAL_10855569737, prime_fortyAL_1388257266599051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464007 : Nat.totient 47290675364112890700454464007 = 40534864388290689278599257624 := by
  rw [← show ((([(7, 1), (193465039, 1), (34920059982009677359, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_7, prime_fortyAL_193465039, prime_fortyAL_34920059982009677359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464008 : Nat.totient 47290675364112890700454464008 = 23645173098297522210896442048 := by
  rw [← show ((([(2, 3), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_143669, prime_fortyAL_13852339783, prime_fortyAL_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464009 : Nat.totient 47290675364112890700454464009 = 31527116710647463988191549440 := by
  rw [← show ((([(3, 2), (177855893, 1), (1592295421, 1), (18554151617, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_177855893, prime_fortyAL_1592295421, prime_fortyAL_18554151617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464010 : Nat.totient 47290675364112890700454464010 = 18867038531782032696231936000 := by
  rw [← show ((([(2, 1), (5, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_401, prime_fortyAL_11069, prime_fortyAL_53269, prime_fortyAL_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464011 : Nat.totient 47290675364112890700454464011 = 42982419576841593205141593600 := by
  rw [← show ((([(11, 1), (6269, 1), (19141, 1), (35827783237643689169, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_11, prime_fortyAL_6269, prime_fortyAL_19141, prime_fortyAL_35827783237643689169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464012 : Nat.totient 47290675364112890700454464012 = 15763515803474572063079424000 := by
  rw [← show ((([(2, 2), (3, 1), (374681, 1), (27212041, 1), (386519565736481, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_374681, prime_fortyAL_27212041, prime_fortyAL_386519565736481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464013 : Nat.totient 47290675364112890700454464013 = 43628224319240153817699878400 := by
  rw [← show ((([(13, 1), (1931, 1), (20789, 1), (25991599, 1), (3486448808761, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_13, prime_fortyAL_1931, prime_fortyAL_20789, prime_fortyAL_25991599, prime_fortyAL_3486448808761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464014 : Nat.totient 47290675364112890700454464014 = 20267432238308654920777827840 := by
  rw [← show ((([(2, 1), (7, 1), (569284721, 1), (928715773, 1), (6389032997, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_7, prime_fortyAL_569284721, prime_fortyAL_928715773, prime_fortyAL_6389032997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464015 : Nat.totient 47290675364112890700454464015 = 25171550993989369482647012736 := by
  rw [← show ((([(3, 1), (5, 1), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_503, prime_fortyAL_15040590709, prime_fortyAL_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464016 : Nat.totient 47290675364112890700454464016 = 23534468606329811678520594432 := by
  rw [← show ((([(2, 4), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_223, prime_fortyAL_5113, prime_fortyAL_101287, prime_fortyAL_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464017 : Nat.totient 47290675364112890700454464017 = 43729178052127324078636554240 := by
  rw [← show ((([(17, 1), (71, 1), (313, 1), (3469, 1), (36084410004208516523, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_17, prime_fortyAL_71, prime_fortyAL_313, prime_fortyAL_3469, prime_fortyAL_36084410004208516523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464018 : Nat.totient 47290675364112890700454464018 = 15741444341253626736493920480 := by
  rw [← show ((([(2, 1), (3, 2), (733, 1), (25867, 1), (138564817290563326591, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_733, prime_fortyAL_25867, prime_fortyAL_138564817290563326591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464019 : Nat.totient 47290675364112890700454464019 = 44666665659991164670917442560 := by
  rw [← show ((([(19, 1), (397, 1), (2017, 1), (2223839, 1), (1397726399797691, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_19, prime_fortyAL_397, prime_fortyAL_2017, prime_fortyAL_2223839, prime_fortyAL_1397726399797691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464020 : Nat.totient 47290675364112890700454464020 = 18916180150877748968060860416 := by
  rw [← show ((([(2, 2), (5, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_210193, prime_fortyAL_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464021 : Nat.totient 47290675364112890700454464021 = 27023243065205513077634065200 := by
  rw [← show ((([(3, 1), (7, 1), (16304803331431, 1), (138114939280471, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_7, prime_fortyAL_16304803331431, prime_fortyAL_138114939280471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464022 : Nat.totient 47290675364112890700454464022 = 21391548028433671764639744000 := by
  rw [← show ((([(2, 1), (11, 1), (457, 1), (541, 1), (1409, 1), (9221, 1), (1363189, 1), (490901413, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_11, prime_fortyAL_457, prime_fortyAL_541, prime_fortyAL_1409, prime_fortyAL_9221, prime_fortyAL_1363189, prime_fortyAL_490901413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464023 : Nat.totient 47290675364112890700454464023 = 45195831562584531217558815360 := by
  rw [← show ((([(23, 1), (1171, 1), (458929, 1), (3826002797968790539, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_23, prime_fortyAL_1171, prime_fortyAL_458929, prime_fortyAL_3826002797968790539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464024 : Nat.totient 47290675364112890700454464024 = 15547617939473564325614668800 := by
  rw [← show ((([(2, 3), (3, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_73, prime_fortyAL_13737811, prime_fortyAL_68784581, prime_fortyAL_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464025 : Nat.totient 47290675364112890700454464025 = 37832092064749459108397044800 := by
  rw [← show ((([(5, 2), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_85243, prime_fortyAL_18480383, prime_fortyAL_23255671, prime_fortyAL_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464026 : Nat.totient 47290675364112890700454464026 = 21826382798805270041685288960 := by
  rw [← show ((([(2, 1), (13, 2), (263761, 1), (8408707693, 1), (63083964649, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_13, prime_fortyAL_263761, prime_fortyAL_8408707693, prime_fortyAL_63083964649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464027 : Nat.totient 47290675364112890700454464027 = 31527116720648676180971266536 := by
  rw [← show ((([(3, 3), (167022307, 1), (10486662089795850443, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_167022307, prime_fortyAL_10486662089795850443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464028 : Nat.totient 47290675364112890700454464028 = 20237317220736087977687938560 := by
  rw [← show ((([(2, 2), (7, 1), (673, 1), (889647091, 1), (2820880298726107, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_7, prime_fortyAL_673, prime_fortyAL_889647091, prime_fortyAL_2820880298726107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464029 : Nat.totient 47290675364112890700454464029 = 45331473482245648639681476912 := by
  rw [← show ((([(29, 1), (139, 1), (11731747795612227908820259, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_29, prime_fortyAL_139, prime_fortyAL_11731747795612227908820259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464030 : Nat.totient 47290675364112890700454464030 = 12610846763763437520121190400 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464031 : Nat.totient 47290675364112890700454464031 = 45634037415781364166073065120 := by
  rw [← show ((([(31, 1), (349, 1), (4371076380821969747708149, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_31, prime_fortyAL_349, prime_fortyAL_4371076380821969747708149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464032 : Nat.totient 47290675364112890700454464032 = 23645337682056445350227232000 := by
  rw [← show ((([(2, 5), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464033 : Nat.totient 47290675364112890700454464033 = 28500897965997337902902552640 := by
  rw [← show ((([(3, 1), (11, 1), (179, 1), (15173528663, 1), (527620858239613, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_11, prime_fortyAL_179, prime_fortyAL_15173528663, prime_fortyAL_527620858239613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464034 : Nat.totient 47290675364112890700454464034 = 22219690299709146537467750400 := by
  rw [← show ((([(2, 1), (17, 1), (1193, 1), (1783, 1), (6547, 1), (98507, 1), (1013900596351, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_17, prime_fortyAL_1193, prime_fortyAL_1783, prime_fortyAL_6547, prime_fortyAL_98507, prime_fortyAL_1013900596351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464035 : Nat.totient 47290675364112890700454464035 = 32017412036724470803742810112 := by
  rw [← show ((([(5, 1), (7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_7, prime_fortyAL_79, prime_fortyAL_1272241326337, prime_fortyAL_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464036 : Nat.totient 47290675364112890700454464036 = 15763558454638016359467211824 := by
  rw [← show ((([(2, 2), (3, 2), (237841108607, 1), (5523140549247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_237841108607, prime_fortyAL_5523140549247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464037 : Nat.totient 47290675364112890700454464037 = 45855509586528429761385223872 := by
  rw [← show ((([(37, 1), (293, 1), (4362206010895018051882157, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_37, prime_fortyAL_293, prime_fortyAL_4362206010895018051882157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464038 : Nat.totient 47290675364112890700454464038 = 22400664696218778578489520000 := by
  rw [← show ((([(2, 1), (19, 1), (123401, 1), (10084938184863487564601, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_19, prime_fortyAL_123401, prime_fortyAL_10084938184863487564601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464039 : Nat.totient 47290675364112890700454464039 = 29015507934729358420723752960 := by
  rw [← show ((([(3, 1), (13, 1), (337, 1), (321721, 1), (11184114340779081913, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_13, prime_fortyAL_337, prime_fortyAL_321721, prime_fortyAL_11184114340779081913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464040 : Nat.totient 47290675364112890700454464040 = 18728877245652730232015619072 := by
  rw [← show ((([(2, 3), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_103, prime_fortyAL_5009, prime_fortyAL_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464041 : Nat.totient 47290675364112890700454464041 = 46137035386952074487649564160 := by
  rw [← show ((([(41, 1), (220889, 1), (5221767975959770844009, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_41, prime_fortyAL_220889, prime_fortyAL_5221767975959770844009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464042 : Nat.totient 47290675364112890700454464042 = 13511272301655791381217192960 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (39607, 1), (1719547, 1), (82478129, 1), (200447861, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_7, prime_fortyAL_39607, prime_fortyAL_1719547, prime_fortyAL_82478129, prime_fortyAL_200447861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464043 : Nat.totient 47290675364112890700454464043 = 46190892024302117969512115424 := by
  rw [← show ((([(43, 1), (240818197, 1), (4566860651326217533, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_43, prime_fortyAL_240818197, prime_fortyAL_4566860651326217533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464044 : Nat.totient 47290675364112890700454464044 = 21495761529142223045661120000 := by
  rw [← show ((([(2, 2), (11, 1), (1074788076457111152283056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_11, prime_fortyAL_1074788076457111152283056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464045 : Nat.totient 47290675364112890700454464045 = 25061015953065107927415255552 := by
  rw [← show ((([(3, 2), (5, 1), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_227, prime_fortyAL_509, prime_fortyAL_106363, prime_fortyAL_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464046 : Nat.totient 47290675364112890700454464046 = 22273840472311341637723043616 := by
  rw [← show ((([(2, 1), (23, 1), (67, 1), (3797, 1), (4041125004773645601599, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_23, prime_fortyAL_67, prime_fortyAL_3797, prime_fortyAL_4041125004773645601599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464047 : Nat.totient 47290675364112890700454464047 = 46284487196598873854725849600 := by
  rw [← show ((([(47, 1), (12909521, 1), (77941279325171544881, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_47, prime_fortyAL_12909521, prime_fortyAL_77941279325171544881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464048 : Nat.totient 47290675364112890700454464048 = 15682048430677405310133927936 := by
  rw [← show ((([(2, 4), (3, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_283, prime_fortyAL_613, prime_fortyAL_85303, prime_fortyAL_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464049 : Nat.totient 47290675364112890700454464049 = 40521211898384369801938627968 := by
  rw [← show ((([(7, 2), (2969, 1), (325064272063794520937129, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_7, prime_fortyAL_2969, prime_fortyAL_325064272063794520937129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464050 : Nat.totient 47290675364112890700454464050 = 18720983448928097847799520000 := by
  rw [← show ((([(2, 1), (5, 2), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_107, prime_fortyAL_1013, prime_fortyAL_144417341, prime_fortyAL_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464051 : Nat.totient 47290675364112890700454464051 = 29656115146470046552812748800 := by
  rw [← show ((([(3, 1), (17, 1), (1873, 1), (47797, 1), (10876741, 1), (952287616681, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_17, prime_fortyAL_1873, prime_fortyAL_47797, prime_fortyAL_10876741, prime_fortyAL_952287616681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464052 : Nat.totient 47290675364112890700454464052 = 21826465552667488015594368000 := by
  rw [← show ((([(2, 2), (13, 1), (909436064694478667316432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_13, prime_fortyAL_909436064694478667316432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464053 : Nat.totient 47290675364112890700454464053 = 46398398470450383328747776000 := by
  rw [← show ((([(53, 1), (892276893662507371706688001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_53, prime_fortyAL_892276893662507371706688001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464054 : Nat.totient 47290675364112890700454464054 = 15576955815502448333459716608 := by
  rw [← show ((([(2, 1), (3, 4), (89, 1), (1723, 1), (35573, 1), (53513668657618357, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_89, prime_fortyAL_1723, prime_fortyAL_35573, prime_fortyAL_53513668657618357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464055 : Nat.totient 47290675364112890700454464055 = 34392815148677213784000430080 := by
  rw [← show ((([(5, 1), (11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_11, prime_fortyAL_85313, prime_fortyAL_219959393, prime_fortyAL_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464056 : Nat.totient 47290675364112890700454464056 = 20087705161651515460698931200 := by
  rw [← show ((([(2, 3), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_7, prime_fortyAL_113, prime_fortyAL_54421, prime_fortyAL_97654321, prime_fortyAL_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464057 : Nat.totient 47290675364112890700454464057 = 29867792602542412064891432400 := by
  rw [← show ((([(3, 1), (19, 1), (12633011, 1), (65674048039713268091, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_19, prime_fortyAL_12633011, prime_fortyAL_65674048039713268091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464058 : Nat.totient 47290675364112890700454464058 = 22829981210261395510564224000 := by
  rw [← show ((([(2, 1), (29, 1), (815356471795049839663008001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_29, prime_fortyAL_815356471795049839663008001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464059 : Nat.totient 47290675364112890700454464059 = 46353156926482562794889565600 := by
  rw [← show ((([(59, 1), (359, 1), (7151, 1), (19312207, 1), (16167034690327, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_59, prime_fortyAL_359, prime_fortyAL_7151, prime_fortyAL_19312207, prime_fortyAL_16167034690327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464060 : Nat.totient 47290675364112890700454464060 = 12572397834087191297154048000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_421, prime_fortyAL_1483, prime_fortyAL_2072201, prime_fortyAL_2567179, prime_fortyAL_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464061 : Nat.totient 47290675364112890700454464061 = 46515418390930712164381436400 := by
  rw [← show ((([(61, 2), (12709130707904566165131541, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_61, prime_fortyAL_12709130707904566165131541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464062 : Nat.totient 47290675364112890700454464062 = 22882584853598688045768123000 := by
  rw [← show ((([(2, 1), (31, 1), (5502598141231, 1), (138616851326671, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_31, prime_fortyAL_5502598141231, prime_fortyAL_138616851326671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464063 : Nat.totient 47290675364112890700454464063 = 27023243065207366114545408000 := by
  rw [← show ((([(3, 2), (7, 1), (750645640700204614292928001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_7, prime_fortyAL_750645640700204614292928001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464064 : Nat.totient 47290675364112890700454464064 = 23360437581727748616583884800 := by
  rw [← show ((([(2, 6), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_83, prime_fortyAL_1433741, prime_fortyAL_106163831, prime_fortyAL_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464065 : Nat.totient 47290675364112890700454464065 = 34791281877386544455086755840 := by
  rw [← show ((([(5, 1), (13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_13, prime_fortyAL_307, prime_fortyAL_2011, prime_fortyAL_100888969, prime_fortyAL_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464066 : Nat.totient 47290675364112890700454464066 = 14247672381550914696931451840 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (173, 1), (4141765227195033342131237, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_11, prime_fortyAL_173, prime_fortyAL_4141765227195033342131237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464067 : Nat.totient 47290675364112890700454464067 = 47106664951989860189125171200 := by
  rw [← show ((([(257, 1), (21951611911, 1), (8382546608565221, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_257, prime_fortyAL_21951611911, prime_fortyAL_8382546608565221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464068 : Nat.totient 47290675364112890700454464068 = 22254435464550222807481075200 := by
  rw [← show ((([(2, 2), (17, 1), (24330664621, 1), (28583317353999781, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_17, prime_fortyAL_24330664621, prime_fortyAL_28583317353999781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464069 : Nat.totient 47290675364112890700454464069 = 30129372866899574528651785152 := by
  rw [← show ((([(3, 1), (23, 1), (1117, 1), (13813439, 1), (44419272177508427, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_23, prime_fortyAL_1117, prime_fortyAL_13813439, prime_fortyAL_44419272177508427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464070 : Nat.totient 47290675364112890700454464070 = 16199029605601766108774387808 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_7, prime_fortyAL_1087, prime_fortyAL_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464071 : Nat.totient 47290675364112890700454464071 = 46802384424920200692167313408 := by
  rw [← show ((([(97, 1), (61729, 1), (7897952918603962932167, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_97, prime_fortyAL_61729, prime_fortyAL_7897952918603962932167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464072 : Nat.totient 47290675364112890700454464072 = 15735419455154738074399153152 := by
  rw [← show ((([(2, 3), (3, 2), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_569, prime_fortyAL_37039, prime_fortyAL_1544987, prime_fortyAL_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464073 : Nat.totient 47290675364112890700454464073 = 47290648958268642132322100688 := by
  rw [← show ((([(1790917, 1), (26405844248568130572469, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_1790917, prime_fortyAL_26405844248568130572469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464074 : Nat.totient 47290675364112890700454464074 = 23006274501385966776277521600 := by
  rw [← show ((([(2, 1), (37, 1), (309443352821, 1), (2065202483007581, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_37, prime_fortyAL_309443352821, prime_fortyAL_2065202483007581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464075 : Nat.totient 47290675364112890700454464075 = 25221314631257463500377739520 := by
  rw [← show ((([(3, 1), (5, 2), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_66569, prime_fortyAL_1596046247, prime_fortyAL_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464076 : Nat.totient 47290675364112890700454464076 = 22400836868545842319131133440 := by
  rw [← show ((([(2, 2), (19, 1), (2428859, 1), (167470561, 1), (1529752406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_19, prime_fortyAL_2428859, prime_fortyAL_167470561, prime_fortyAL_1529752406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464077 : Nat.totient 47290675364112890700454464077 = 36841729686711793889123232000 := by
  rw [← show ((([(7, 1), (11, 1), (4523, 1), (320918551601, 1), (423119830387, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_7, prime_fortyAL_11, prime_fortyAL_4523, prime_fortyAL_320918551601, prime_fortyAL_423119830387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464078 : Nat.totient 47290675364112890700454464078 = 14550977035111658677062912000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (606290709796319111544288001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_13, prime_fortyAL_606290709796319111544288001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464079 : Nat.totient 47290675364112890700454464079 = 47226624849672288041827636320 := by
  rw [← show ((([(743, 1), (117413, 1), (542088903902523452581, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_743, prime_fortyAL_117413, prime_fortyAL_542088903902523452581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464080 : Nat.totient 47290675364112890700454464080 = 18916270130173191852230595200 := by
  rw [← show ((([(2, 4), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_1222615931, prime_fortyAL_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464081 : Nat.totient 47290675364112890700454464081 = 31527116909358564654713507040 := by
  rw [← show ((([(3, 3), (630317946683, 1), (2778766659246041, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_630317946683, prime_fortyAL_2778766659246041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464082 : Nat.totient 47290675364112890700454464082 = 22797485460200382284250885120 := by
  rw [← show ((([(2, 1), (41, 1), (149, 1), (197, 1), (19647584683708272101017, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_41, prime_fortyAL_149, prime_fortyAL_197, prime_fortyAL_19647584683708272101017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464083 : Nat.totient 47290675364112890700454464083 = 47290675364110362276632225880 := by
  rw [← show ((([(18844061505463, 1), (2509579760732741, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_18844061505463, prime_fortyAL_2509579760732741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464084 : Nat.totient 47290675364112890700454464084 = 13511621472624876190069665888 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (225273263, 1), (2499116952574853327, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_7, prime_fortyAL_225273263, prime_fortyAL_2499116952574853327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464085 : Nat.totient 47290675364112890700454464085 = 35556265661525913604044521472 := by
  rw [← show ((([(5, 1), (17, 1), (709, 1), (58337, 1), (13451362101445396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_17, prime_fortyAL_709, prime_fortyAL_58337, prime_fortyAL_13451362101445396397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464086 : Nat.totient 47290675364112890700454464086 = 23075989118916080323377605064 := by
  rw [← show ((([(2, 1), (43, 1), (1187, 1), (463261646167912959194123, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_43, prime_fortyAL_1187, prime_fortyAL_463261646167912959194123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464087 : Nat.totient 47290675364112890700454464087 = 30200288646925258855976908800 := by
  rw [← show ((([(3, 1), (29, 1), (127, 1), (23950417, 1), (181537789, 1), (984401851, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_29, prime_fortyAL_127, prime_fortyAL_23950417, prime_fortyAL_181537789, prime_fortyAL_984401851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464088 : Nat.totient 47290675364112890700454464088 = 21193004323712220233467833600 := by
  rw [← show ((([(2, 3), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_11, prime_fortyAL_71, prime_fortyAL_26687336297, prime_fortyAL_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464089 : Nat.totient 47290675364112890700454464089 = 47253148145899790293148840352 := by
  rw [← show ((([(1289, 1), (56299, 1), (651661281419424648499, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_1289, prime_fortyAL_56299, prime_fortyAL_651661281419424648499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464090 : Nat.totient 47290675364112890700454464090 = 12610846763763437520121190400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_5, prime_fortyAL_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464091 : Nat.totient 47290675364112890700454464091 = 37195308401354664298505994240 := by
  rw [← show ((([(7, 1), (13, 1), (241, 1), (593, 1), (10949, 1), (289517219, 1), (1147132367, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_7, prime_fortyAL_13, prime_fortyAL_241, prime_fortyAL_593, prime_fortyAL_10949, prime_fortyAL_289517219, prime_fortyAL_1147132367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464092 : Nat.totient 47290675364112890700454464092 = 22589996518050324023003175360 := by
  rw [← show ((([(2, 2), (23, 1), (829, 1), (56624411, 1), (10950386820164879, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_23, prime_fortyAL_829, prime_fortyAL_56624411, prime_fortyAL_10950386820164879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464093 : Nat.totient 47290675364112890700454464093 = 30399645296022512044952954880 := by
  rw [← show ((([(3, 1), (31, 1), (277, 1), (94109, 1), (19506602764358177057, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_31, prime_fortyAL_277, prime_fortyAL_94109, prime_fortyAL_19506602764358177057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464094 : Nat.totient 47290675364112890700454464094 = 23142245390948861406605376000 := by
  rw [← show ((([(2, 1), (47, 1), (503092291107583943621856001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_47, prime_fortyAL_503092291107583943621856001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464095 : Nat.totient 47290675364112890700454464095 = 35841353960077854115334421888 := by
  rw [← show ((([(5, 1), (19, 1), (390056504429, 1), (1276216592026469, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_5, prime_fortyAL_19, prime_fortyAL_390056504429, prime_fortyAL_1276216592026469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464096 : Nat.totient 47290675364112890700454464096 = 15618918137677390871498151936 := by
  rw [← show ((([(2, 5), (3, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_3, prime_fortyAL_109, prime_fortyAL_762563, prime_fortyAL_500452427, prime_fortyAL_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464097 : Nat.totient 47290675364112890700454464097 = 46149215448983969957760000000 := by
  rw [← show ((([(73, 1), (101, 1), (1451, 1), (9376751, 1), (471423780705089, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_73, prime_fortyAL_101, prime_fortyAL_1451, prime_fortyAL_9376751, prime_fortyAL_471423780705089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464098 : Nat.totient 47290675364112890700454464098 = 20267432298905524585909056000 := by
  rw [← show ((([(2, 1), (7, 2), (482557911878702966331168001, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_7, prime_fortyAL_482557911878702966331168001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464099 : Nat.totient 47290675364112890700454464099 = 28660943172922247997726126000 := by
  rw [← show ((([(3, 2), (11, 1), (396971, 1), (1203321123045496636931, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_3, prime_fortyAL_11, prime_fortyAL_396971, prime_fortyAL_1203321123045496636931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyAL_47290675364112890700454464100 : Nat.totient 47290675364112890700454464100 = 18832753673753496183975381120 := by
  rw [← show ((([(2, 2), (5, 2), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112890700454464100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyAL_2, prime_fortyAL_5, prime_fortyAL_239, prime_fortyAL_4327, prime_fortyAL_1214459, prime_fortyAL_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyAL : certifiedKill 1 47290675364112890700454463999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyAL_47290675364112890700454464000, phi_fortyAL_47290675364112890700454464001, phi_fortyAL_47290675364112890700454464002,
    phi_fortyAL_47290675364112890700454464003, phi_fortyAL_47290675364112890700454464004, phi_fortyAL_47290675364112890700454464005,
    phi_fortyAL_47290675364112890700454464006, phi_fortyAL_47290675364112890700454464007, phi_fortyAL_47290675364112890700454464008,
    phi_fortyAL_47290675364112890700454464009, phi_fortyAL_47290675364112890700454464010, phi_fortyAL_47290675364112890700454464011,
    phi_fortyAL_47290675364112890700454464012, phi_fortyAL_47290675364112890700454464013, phi_fortyAL_47290675364112890700454464014,
    phi_fortyAL_47290675364112890700454464015, phi_fortyAL_47290675364112890700454464016, phi_fortyAL_47290675364112890700454464017,
    phi_fortyAL_47290675364112890700454464018, phi_fortyAL_47290675364112890700454464019, phi_fortyAL_47290675364112890700454464020,
    phi_fortyAL_47290675364112890700454464021, phi_fortyAL_47290675364112890700454464022, phi_fortyAL_47290675364112890700454464023,
    phi_fortyAL_47290675364112890700454464024, phi_fortyAL_47290675364112890700454464025, phi_fortyAL_47290675364112890700454464026,
    phi_fortyAL_47290675364112890700454464027, phi_fortyAL_47290675364112890700454464028, phi_fortyAL_47290675364112890700454464029,
    phi_fortyAL_47290675364112890700454464030, phi_fortyAL_47290675364112890700454464031, phi_fortyAL_47290675364112890700454464032,
    phi_fortyAL_47290675364112890700454464033, phi_fortyAL_47290675364112890700454464034, phi_fortyAL_47290675364112890700454464035,
    phi_fortyAL_47290675364112890700454464036, phi_fortyAL_47290675364112890700454464037, phi_fortyAL_47290675364112890700454464038,
    phi_fortyAL_47290675364112890700454464039, phi_fortyAL_47290675364112890700454464040, phi_fortyAL_47290675364112890700454464041,
    phi_fortyAL_47290675364112890700454464042, phi_fortyAL_47290675364112890700454464043, phi_fortyAL_47290675364112890700454464044,
    phi_fortyAL_47290675364112890700454464045, phi_fortyAL_47290675364112890700454464046, phi_fortyAL_47290675364112890700454464047,
    phi_fortyAL_47290675364112890700454464048, phi_fortyAL_47290675364112890700454464049, phi_fortyAL_47290675364112890700454464050,
    phi_fortyAL_47290675364112890700454464051, phi_fortyAL_47290675364112890700454464052, phi_fortyAL_47290675364112890700454464053,
    phi_fortyAL_47290675364112890700454464054, phi_fortyAL_47290675364112890700454464055, phi_fortyAL_47290675364112890700454464056,
    phi_fortyAL_47290675364112890700454464057, phi_fortyAL_47290675364112890700454464058, phi_fortyAL_47290675364112890700454464059,
    phi_fortyAL_47290675364112890700454464060, phi_fortyAL_47290675364112890700454464061, phi_fortyAL_47290675364112890700454464062,
    phi_fortyAL_47290675364112890700454464063, phi_fortyAL_47290675364112890700454464064, phi_fortyAL_47290675364112890700454464065,
    phi_fortyAL_47290675364112890700454464066, phi_fortyAL_47290675364112890700454464067, phi_fortyAL_47290675364112890700454464068,
    phi_fortyAL_47290675364112890700454464069, phi_fortyAL_47290675364112890700454464070, phi_fortyAL_47290675364112890700454464071,
    phi_fortyAL_47290675364112890700454464072, phi_fortyAL_47290675364112890700454464073, phi_fortyAL_47290675364112890700454464074,
    phi_fortyAL_47290675364112890700454464075, phi_fortyAL_47290675364112890700454464076, phi_fortyAL_47290675364112890700454464077,
    phi_fortyAL_47290675364112890700454464078, phi_fortyAL_47290675364112890700454464079, phi_fortyAL_47290675364112890700454464080,
    phi_fortyAL_47290675364112890700454464081, phi_fortyAL_47290675364112890700454464082, phi_fortyAL_47290675364112890700454464083,
    phi_fortyAL_47290675364112890700454464084, phi_fortyAL_47290675364112890700454464085, phi_fortyAL_47290675364112890700454464086,
    phi_fortyAL_47290675364112890700454464087, phi_fortyAL_47290675364112890700454464088, phi_fortyAL_47290675364112890700454464089,
    phi_fortyAL_47290675364112890700454464090, phi_fortyAL_47290675364112890700454464091, phi_fortyAL_47290675364112890700454464092,
    phi_fortyAL_47290675364112890700454464093, phi_fortyAL_47290675364112890700454464094, phi_fortyAL_47290675364112890700454464095,
    phi_fortyAL_47290675364112890700454464096, phi_fortyAL_47290675364112890700454464097, phi_fortyAL_47290675364112890700454464098,
    phi_fortyAL_47290675364112890700454464099, phi_fortyAL_47290675364112890700454464100]

end TotientTailPeriodKiller
end Erdos249257
