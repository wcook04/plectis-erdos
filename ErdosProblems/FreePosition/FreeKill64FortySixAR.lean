import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 46P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortySixARFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortySixARFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortySixARFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortySixARFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortySixARFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortySixARFastPow a n * fortySixARFastPow a n * a
        else fortySixARFastPow a n * fortySixARFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortySixAR_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortySixAR_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortySixAR_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortySixAR_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortySixAR_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortySixAR_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortySixAR_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortySixAR_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortySixAR_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortySixAR_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortySixAR_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortySixAR_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortySixAR_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortySixAR_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortySixAR_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortySixAR_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortySixAR_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortySixAR_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortySixAR_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortySixAR_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortySixAR_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortySixAR_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortySixAR_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortySixAR_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortySixAR_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortySixAR_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortySixAR_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortySixAR_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortySixAR_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortySixAR_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortySixAR_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortySixAR_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortySixAR_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortySixAR_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortySixAR_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortySixAR_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortySixAR_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortySixAR_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortySixAR_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortySixAR_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortySixAR_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortySixAR_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortySixAR_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortySixAR_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortySixAR_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortySixAR_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortySixAR_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortySixAR_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortySixAR_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortySixAR_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortySixAR_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortySixAR_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortySixAR_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortySixAR_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortySixAR_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortySixAR_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortySixAR_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortySixAR_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortySixAR_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortySixAR_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortySixAR_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortySixAR_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortySixAR_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortySixAR_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortySixAR_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortySixAR_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortySixAR_431 : Nat.Prime 431 := by norm_num
private theorem prime_fortySixAR_433 : Nat.Prime 433 := by norm_num
private theorem prime_fortySixAR_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortySixAR_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortySixAR_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortySixAR_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortySixAR_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortySixAR_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortySixAR_521 : Nat.Prime 521 := by norm_num
private theorem prime_fortySixAR_547 : Nat.Prime 547 := by norm_num
private theorem prime_fortySixAR_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortySixAR_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortySixAR_569 : Nat.Prime 569 := by norm_num
private theorem prime_fortySixAR_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortySixAR_587 : Nat.Prime 587 := by norm_num
private theorem prime_fortySixAR_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortySixAR_607 : Nat.Prime 607 := by norm_num
private theorem prime_fortySixAR_617 : Nat.Prime 617 := by norm_num
private theorem prime_fortySixAR_619 : Nat.Prime 619 := by norm_num
private theorem prime_fortySixAR_631 : Nat.Prime 631 := by norm_num
private theorem prime_fortySixAR_641 : Nat.Prime 641 := by norm_num
private theorem prime_fortySixAR_653 : Nat.Prime 653 := by norm_num
private theorem prime_fortySixAR_661 : Nat.Prime 661 := by norm_num
private theorem prime_fortySixAR_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortySixAR_701 : Nat.Prime 701 := by norm_num
private theorem prime_fortySixAR_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortySixAR_733 : Nat.Prime 733 := by norm_num
private theorem prime_fortySixAR_739 : Nat.Prime 739 := by norm_num
private theorem prime_fortySixAR_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortySixAR_787 : Nat.Prime 787 := by norm_num
private theorem prime_fortySixAR_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortySixAR_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortySixAR_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortySixAR_883 : Nat.Prime 883 := by norm_num
private theorem prime_fortySixAR_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortySixAR_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fortySixAR_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fortySixAR_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_fortySixAR_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortySixAR_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fortySixAR_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fortySixAR_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fortySixAR_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fortySixAR_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_fortySixAR_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_fortySixAR_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fortySixAR_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fortySixAR_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fortySixAR_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fortySixAR_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_fortySixAR_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fortySixAR_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_fortySixAR_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fortySixAR_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_fortySixAR_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_fortySixAR_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_fortySixAR_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortySixAR_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_fortySixAR_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_fortySixAR_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_fortySixAR_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_fortySixAR_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_fortySixAR_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_fortySixAR_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_fortySixAR_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_fortySixAR_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_fortySixAR_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_fortySixAR_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_fortySixAR_1987 : Nat.Prime 1987 := by norm_num
private theorem prime_fortySixAR_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_fortySixAR_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_fortySixAR_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_fortySixAR_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fortySixAR_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_fortySixAR_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_fortySixAR_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_fortySixAR_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_fortySixAR_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortySixAR_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_fortySixAR_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_fortySixAR_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_fortySixAR_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_fortySixAR_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_fortySixAR_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_fortySixAR_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fortySixAR_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fortySixAR_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_fortySixAR_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_fortySixAR_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_fortySixAR_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_fortySixAR_3907 : Nat.Prime 3907 := by norm_num
private theorem prime_fortySixAR_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_fortySixAR_4349 : Nat.Prime 4349 := by norm_num
private theorem prime_fortySixAR_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_fortySixAR_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortySixAR_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_fortySixAR_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_fortySixAR_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_fortySixAR_5651 : Nat.Prime 5651 := by norm_num
private theorem prime_fortySixAR_5659 : Nat.Prime 5659 := by norm_num
private theorem prime_fortySixAR_6007 : Nat.Prime 6007 := by norm_num
private theorem prime_fortySixAR_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_fortySixAR_6301 : Nat.Prime 6301 := by norm_num
private theorem prime_fortySixAR_6311 : Nat.Prime 6311 := by norm_num
private theorem prime_fortySixAR_6317 : Nat.Prime 6317 := by norm_num
private theorem prime_fortySixAR_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fortySixAR_6361 : Nat.Prime 6361 := by norm_num
private theorem prime_fortySixAR_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_fortySixAR_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_fortySixAR_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_fortySixAR_6553 : Nat.Prime 6553 := by norm_num
private theorem prime_fortySixAR_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortySixAR_6977 : Nat.Prime 6977 := by norm_num
private theorem prime_fortySixAR_7159 : Nat.Prime 7159 := by norm_num
private theorem prime_fortySixAR_7283 : Nat.Prime 7283 := by norm_num
private theorem prime_fortySixAR_7297 : Nat.Prime 7297 := by norm_num
private theorem prime_fortySixAR_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_fortySixAR_7517 : Nat.Prime 7517 := by norm_num
private theorem prime_fortySixAR_7907 : Nat.Prime 7907 := by norm_num
private theorem prime_fortySixAR_7993 : Nat.Prime 7993 := by norm_num
private theorem prime_fortySixAR_8263 : Nat.Prime 8263 := by norm_num
private theorem prime_fortySixAR_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_fortySixAR_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_fortySixAR_9173 : Nat.Prime 9173 := by norm_num
private theorem prime_fortySixAR_9221 : Nat.Prime 9221 := by norm_num
private theorem prime_fortySixAR_9349 : Nat.Prime 9349 := by norm_num
private theorem prime_fortySixAR_9413 : Nat.Prime 9413 := by norm_num
private theorem prime_fortySixAR_9551 : Nat.Prime 9551 := by norm_num
private theorem prime_fortySixAR_9679 : Nat.Prime 9679 := by norm_num
private theorem prime_fortySixAR_9811 : Nat.Prime 9811 := by norm_num
private theorem prime_fortySixAR_10289 : Nat.Prime 10289 := by norm_num
private theorem prime_fortySixAR_10343 : Nat.Prime 10343 := by norm_num
private theorem prime_fortySixAR_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_fortySixAR_11657 : Nat.Prime 11657 := by norm_num
private theorem prime_fortySixAR_12113 : Nat.Prime 12113 := by norm_num
private theorem prime_fortySixAR_12433 : Nat.Prime 12433 := by norm_num
private theorem prime_fortySixAR_12697 : Nat.Prime 12697 := by norm_num
private theorem prime_fortySixAR_12829 : Nat.Prime 12829 := by norm_num
private theorem prime_fortySixAR_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_fortySixAR_12893 : Nat.Prime 12893 := by norm_num
private theorem prime_fortySixAR_13177 : Nat.Prime 13177 := by norm_num
private theorem prime_fortySixAR_13613 : Nat.Prime 13613 := by norm_num
private theorem prime_fortySixAR_13799 : Nat.Prime 13799 := by norm_num
private theorem prime_fortySixAR_14419 : Nat.Prime 14419 := by norm_num
private theorem prime_fortySixAR_14887 : Nat.Prime 14887 := by norm_num
private theorem prime_fortySixAR_14929 : Nat.Prime 14929 := by norm_num
private theorem prime_fortySixAR_15377 : Nat.Prime 15377 := by norm_num
private theorem prime_fortySixAR_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_fortySixAR_18061 : Nat.Prime 18061 := by norm_num
private theorem prime_fortySixAR_20129 : Nat.Prime 20129 := by norm_num
private theorem prime_fortySixAR_20593 : Nat.Prime 20593 := by norm_num
private theorem prime_fortySixAR_21649 : Nat.Prime 21649 := by norm_num
private theorem prime_fortySixAR_23369 : Nat.Prime 23369 := by norm_num
private theorem prime_fortySixAR_25741 : Nat.Prime 25741 := by norm_num
private theorem prime_fortySixAR_26041 : Nat.Prime 26041 := by norm_num
private theorem prime_fortySixAR_26339 : Nat.Prime 26339 := by norm_num
private theorem prime_fortySixAR_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_fortySixAR_27583 : Nat.Prime 27583 := by norm_num
private theorem prime_fortySixAR_28949 : Nat.Prime 28949 := by norm_num
private theorem prime_fortySixAR_29803 : Nat.Prime 29803 := by norm_num
private theorem prime_fortySixAR_32533 : Nat.Prime 32533 := by norm_num
private theorem prime_fortySixAR_32633 : Nat.Prime 32633 := by norm_num
private theorem prime_fortySixAR_34337 : Nat.Prime 34337 := by norm_num
private theorem prime_fortySixAR_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortySixAR_36599 : Nat.Prime 36599 := by norm_num
private theorem prime_fortySixAR_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortySixAR_38803 : Nat.Prime 38803 := by norm_num
private theorem prime_fortySixAR_39679 : Nat.Prime 39679 := by norm_num
private theorem prime_fortySixAR_40771 : Nat.Prime 40771 := by norm_num
private theorem prime_fortySixAR_44417 : Nat.Prime 44417 := by norm_num
private theorem prime_fortySixAR_44647 : Nat.Prime 44647 := by norm_num
private theorem prime_fortySixAR_49199 : Nat.Prime 49199 := by norm_num
private theorem prime_fortySixAR_49481 : Nat.Prime 49481 := by norm_num
private theorem prime_fortySixAR_52051 : Nat.Prime 52051 := by norm_num
private theorem prime_fortySixAR_53597 : Nat.Prime 53597 := by norm_num
private theorem prime_fortySixAR_53633 : Nat.Prime 53633 := by norm_num
private theorem prime_fortySixAR_53731 : Nat.Prime 53731 := by norm_num
private theorem prime_fortySixAR_53819 : Nat.Prime 53819 := by norm_num
private theorem prime_fortySixAR_55217 : Nat.Prime 55217 := by norm_num
private theorem prime_fortySixAR_55603 : Nat.Prime 55603 := by norm_num
private theorem prime_fortySixAR_56437 : Nat.Prime 56437 := by norm_num
private theorem prime_fortySixAR_57719 : Nat.Prime 57719 := by norm_num
private theorem prime_fortySixAR_60083 : Nat.Prime 60083 := by norm_num
private theorem prime_fortySixAR_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortySixAR_63667 : Nat.Prime 63667 := by norm_num
private theorem prime_fortySixAR_65119 : Nat.Prime 65119 := by norm_num
private theorem prime_fortySixAR_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_fortySixAR_69233 : Nat.Prime 69233 := by norm_num
private theorem prime_fortySixAR_72139 : Nat.Prime 72139 := by norm_num
private theorem prime_fortySixAR_72227 : Nat.Prime 72227 := by norm_num
private theorem prime_fortySixAR_72671 : Nat.Prime 72671 := by norm_num
private theorem prime_fortySixAR_74561 : Nat.Prime 74561 := by norm_num
private theorem prime_fortySixAR_76949 : Nat.Prime 76949 := by norm_num
private theorem prime_fortySixAR_77017 : Nat.Prime 77017 := by norm_num
private theorem prime_fortySixAR_80657 : Nat.Prime 80657 := by norm_num
private theorem prime_fortySixAR_85091 : Nat.Prime 85091 := by norm_num
private theorem prime_fortySixAR_86467 : Nat.Prime 86467 := by norm_num
private theorem prime_fortySixAR_87641 : Nat.Prime 87641 := by norm_num
private theorem prime_fortySixAR_89513 : Nat.Prime 89513 := by norm_num
private theorem prime_fortySixAR_92941 : Nat.Prime 92941 := by norm_num
private theorem prime_fortySixAR_100511 : Nat.Prime 100511 := by norm_num
private theorem prime_fortySixAR_101807 : Nat.Prime 101807 := by norm_num
private theorem prime_fortySixAR_103333 : Nat.Prime 103333 := by norm_num
private theorem prime_fortySixAR_104009 : Nat.Prime 104009 := by norm_num
private theorem prime_fortySixAR_107099 : Nat.Prime 107099 := by norm_num
private theorem prime_fortySixAR_107339 : Nat.Prime 107339 := by norm_num
private theorem prime_fortySixAR_112939 : Nat.Prime 112939 := by norm_num
private theorem prime_fortySixAR_113623 : Nat.Prime 113623 := by norm_num
private theorem prime_fortySixAR_113903 : Nat.Prime 113903 := by norm_num
private theorem prime_fortySixAR_116927 : Nat.Prime 116927 := by norm_num
private theorem prime_fortySixAR_120011 : Nat.Prime 120011 := by norm_num
private theorem prime_fortySixAR_129671 : Nat.Prime 129671 := by norm_num
private theorem prime_fortySixAR_130303 : Nat.Prime 130303 := by norm_num
private theorem prime_fortySixAR_136303 : Nat.Prime 136303 := by norm_num
private theorem prime_fortySixAR_143467 : Nat.Prime 143467 := by norm_num
private theorem prime_fortySixAR_149323 : Nat.Prime 149323 := by norm_num
private theorem prime_fortySixAR_149341 : Nat.Prime 149341 := by norm_num
private theorem prime_fortySixAR_153929 : Nat.Prime 153929 := by norm_num
private theorem prime_fortySixAR_154589 : Nat.Prime 154589 := by norm_num
private theorem prime_fortySixAR_179383 : Nat.Prime 179383 := by norm_num
private theorem prime_fortySixAR_181499 : Nat.Prime 181499 := by norm_num
private theorem prime_fortySixAR_192461 : Nat.Prime 192461 := by norm_num
private theorem prime_fortySixAR_195259 : Nat.Prime 195259 := by norm_num
private theorem prime_fortySixAR_196541 : Nat.Prime 196541 := by norm_num
private theorem prime_fortySixAR_198223 : Nat.Prime 198223 := by norm_num
private theorem prime_fortySixAR_202639 : Nat.Prime 202639 := by norm_num
private theorem prime_fortySixAR_203051 : Nat.Prime 203051 := by norm_num
private theorem prime_fortySixAR_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fortySixAR_214691 : Nat.Prime 214691 := by norm_num
private theorem prime_fortySixAR_228139 : Nat.Prime 228139 := by norm_num
private theorem prime_fortySixAR_229699 : Nat.Prime 229699 := by norm_num
private theorem prime_fortySixAR_243311 : Nat.Prime 243311 := by norm_num
private theorem prime_fortySixAR_261031 : Nat.Prime 261031 := by norm_num
private theorem prime_fortySixAR_263503 : Nat.Prime 263503 := by norm_num
private theorem prime_fortySixAR_288979 : Nat.Prime 288979 := by norm_num
private theorem prime_fortySixAR_305351 : Nat.Prime 305351 := by norm_num
private theorem prime_fortySixAR_394813 : Nat.Prime 394813 := by norm_num
private theorem prime_fortySixAR_399389 : Nat.Prime 399389 := by norm_num
private theorem prime_fortySixAR_400943 : Nat.Prime 400943 := by norm_num
private theorem prime_fortySixAR_429127 : Nat.Prime 429127 := by norm_num
private theorem prime_fortySixAR_493931 : Nat.Prime 493931 := by norm_num
private theorem prime_fortySixAR_500029 : Nat.Prime 500029 := by norm_num
private theorem prime_fortySixAR_529471 : Nat.Prime 529471 := by norm_num
private theorem prime_fortySixAR_535939 : Nat.Prime 535939 := by norm_num
private theorem prime_fortySixAR_541991 : Nat.Prime 541991 := by norm_num
private theorem prime_fortySixAR_546289 : Nat.Prime 546289 := by norm_num
private theorem prime_fortySixAR_574913 : Nat.Prime 574913 := by norm_num
private theorem prime_fortySixAR_622603 : Nat.Prime 622603 := by norm_num
private theorem prime_fortySixAR_642113 : Nat.Prime 642113 := by norm_num
private theorem prime_fortySixAR_645179 : Nat.Prime 645179 := by norm_num
private theorem prime_fortySixAR_647557 : Nat.Prime 647557 := by norm_num
private theorem prime_fortySixAR_668599 : Nat.Prime 668599 := by norm_num
private theorem prime_fortySixAR_677311 : Nat.Prime 677311 := by norm_num
private theorem prime_fortySixAR_723053 : Nat.Prime 723053 := by norm_num
private theorem prime_fortySixAR_756593 : Nat.Prime 756593 := by norm_num
private theorem prime_fortySixAR_763739 : Nat.Prime 763739 := by norm_num
private theorem prime_fortySixAR_811651 : Nat.Prime 811651 := by norm_num
private theorem prime_fortySixAR_938207 : Nat.Prime 938207 := by norm_num
private theorem prime_fortySixAR_945883 : Nat.Prime 945883 := by norm_num
private theorem prime_fortySixAR_946681 : Nat.Prime 946681 := by norm_num
private theorem prime_fortySixAR_989777 : Nat.Prime 989777 := by norm_num
private theorem prime_fortySixAR_1068233 : Nat.Prime 1068233 := by norm_num
private theorem prime_fortySixAR_1076003 : Nat.Prime 1076003 := by norm_num
private theorem prime_fortySixAR_1097909 : Nat.Prime 1097909 := by norm_num
private theorem prime_fortySixAR_1170233 : Nat.Prime 1170233 := by norm_num
private theorem prime_fortySixAR_1216489 : Nat.Prime 1216489 := by norm_num
private theorem prime_fortySixAR_1225507 : Nat.Prime 1225507 := by norm_num
private theorem prime_fortySixAR_1230067 : Nat.Prime 1230067 := by norm_num
private theorem prime_fortySixAR_1276279 : Nat.Prime 1276279 := by norm_num
private theorem prime_fortySixAR_1318897 : Nat.Prime 1318897 := by norm_num
private theorem prime_fortySixAR_1341359 : Nat.Prime 1341359 := by norm_num
private theorem prime_fortySixAR_1469231 : Nat.Prime 1469231 := by norm_num
private theorem prime_fortySixAR_1497787 : Nat.Prime 1497787 := by norm_num
private theorem prime_fortySixAR_1577711 : Nat.Prime 1577711 := by norm_num
private theorem prime_fortySixAR_1611971 : Nat.Prime 1611971 := by norm_num
private theorem prime_fortySixAR_1627651 : Nat.Prime 1627651 := by norm_num
private theorem prime_fortySixAR_1647323 : Nat.Prime 1647323 := by norm_num
private theorem prime_fortySixAR_1969729 : Nat.Prime 1969729 := by norm_num
private theorem prime_fortySixAR_1978189 : Nat.Prime 1978189 := by norm_num
private theorem prime_fortySixAR_2022263 : Nat.Prime 2022263 := by norm_num
private theorem prime_fortySixAR_2039771 : Nat.Prime 2039771 := by norm_num
private theorem prime_fortySixAR_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fortySixAR_2190157 : Nat.Prime 2190157 := by norm_num
private theorem prime_fortySixAR_2428303 : Nat.Prime 2428303 := by norm_num
private theorem prime_fortySixAR_2457311 : Nat.Prime 2457311 := by norm_num
private theorem prime_fortySixAR_2461807 : Nat.Prime 2461807 := by norm_num
private theorem prime_fortySixAR_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fortySixAR_2573803 : Nat.Prime 2573803 := by norm_num
private theorem prime_fortySixAR_2970797 : Nat.Prime 2970797 := by norm_num
private theorem prime_fortySixAR_3625591 : Nat.Prime 3625591 := by norm_num
private theorem prime_fortySixAR_3704279 : Nat.Prime 3704279 := by norm_num
private theorem prime_fortySixAR_4350391 : Nat.Prime 4350391 := by norm_num
private theorem prime_fortySixAR_4454239 : Nat.Prime 4454239 := by norm_num
private theorem prime_fortySixAR_4587361 : Nat.Prime 4587361 := by norm_num
private theorem prime_fortySixAR_4609763 : Nat.Prime 4609763 := by norm_num
private theorem prime_fortySixAR_4661323 : Nat.Prime 4661323 := by norm_num
private theorem prime_fortySixAR_4963961 : Nat.Prime 4963961 := by norm_num
private theorem prime_fortySixAR_4997389 : Nat.Prime 4997389 := by norm_num
private theorem prime_fortySixAR_5100367 : Nat.Prime 5100367 := by norm_num
private theorem prime_fortySixAR_6260129 : Nat.Prime 6260129 := by norm_num
private theorem prime_fortySixAR_6273037 : Nat.Prime 6273037 := by norm_num
private theorem prime_fortySixAR_6780223 : Nat.Prime 6780223 := by norm_num
private theorem prime_fortySixAR_6848701 : Nat.Prime 6848701 := by norm_num
private theorem prime_fortySixAR_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortySixAR_7369849 : Nat.Prime 7369849 := by norm_num
private theorem prime_fortySixAR_7399409 : Nat.Prime 7399409 := by norm_num
private theorem prime_fortySixAR_8472649 : Nat.Prime 8472649 := by norm_num
private theorem prime_fortySixAR_8970263 : Nat.Prime 8970263 := by norm_num
private theorem prime_fortySixAR_9077903 : Nat.Prime 9077903 := by norm_num
private theorem prime_fortySixAR_9262091 : Nat.Prime 9262091 := by norm_num
private theorem prime_fortySixAR_9518681 : Nat.Prime 9518681 := by norm_num
private theorem prime_fortySixAR_9662041 : Nat.Prime 9662041 := by norm_num
private theorem prime_fortySixAR_9822289 : Nat.Prime 9822289 := by norm_num
private theorem prime_fortySixAR_9915313 : Nat.Prime 9915313 := by norm_num
private theorem prime_fortySixAR_10642529 : Nat.Prime 10642529 := by norm_num
private theorem prime_fortySixAR_12064457 : Nat.Prime 12064457 := by norm_num
private theorem prime_fortySixAR_12416689 : Nat.Prime 12416689 := by norm_num
private theorem prime_fortySixAR_12984269 : Nat.Prime 12984269 := by norm_num
private theorem prime_fortySixAR_14521601 : Nat.Prime 14521601 := by norm_num
private theorem prime_fortySixAR_14763709 : Nat.Prime 14763709 := by norm_num
private theorem prime_fortySixAR_15460729 : Nat.Prime 15460729 := by norm_num
private theorem prime_fortySixAR_16027751 : Nat.Prime 16027751 := by norm_num
private theorem prime_fortySixAR_16082593 : Nat.Prime 16082593 := by norm_num
private theorem prime_fortySixAR_16152013 : Nat.Prime 16152013 := by norm_num
private theorem prime_fortySixAR_17199463 : Nat.Prime 17199463 := by norm_num
private theorem prime_fortySixAR_18450109 : Nat.Prime 18450109 := by norm_num
private theorem prime_fortySixAR_18769073 : Nat.Prime 18769073 := by norm_num
private theorem prime_fortySixAR_24478913 : Nat.Prime 24478913 := by norm_num
private theorem prime_fortySixAR_26472557 : Nat.Prime 26472557 := by norm_num
private theorem prime_fortySixAR_28337723 : Nat.Prime 28337723 := by norm_num
private theorem prime_fortySixAR_29419597 : Nat.Prime 29419597 := by norm_num
private theorem prime_fortySixAR_31328573 : Nat.Prime 31328573 := by
  apply lucas_primality 31328573 (2 : ZMod 31328573)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (113, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (113, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) = 31328573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_113
      · exact prime_fortySixAR_6301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31328573) ^ 15664286 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 31328573) ^ 2848052 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 31328573) ^ 277244 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 31328573) ^ 4972 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_34510447 : Nat.Prime 34510447 := by
  apply lucas_primality 34510447 (3 : ZMod 34510447)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (151, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (151, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) = 34510447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_151
      · exact prime_fortySixAR_12697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34510447) ^ 17255223 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 34510447) ^ 11503482 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 34510447) ^ 228546 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 34510447) ^ 2718 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_45098231 : Nat.Prime 45098231 := by
  apply lucas_primality 45098231 (29 : ZMod 45098231)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (85091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (85091, 1)] : List FactorBlock).map factorBlockValue).prod) = 45098231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_85091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 45098231) ^ 22549115 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 9019646 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 850910 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 530 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_46324247 : Nat.Prime 46324247 := by
  apply lucas_primality 46324247 (5 : ZMod 46324247)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (120011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (120011, 1)] : List FactorBlock).map factorBlockValue).prod) = 46324247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_193
      · exact prime_fortySixAR_120011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 46324247) ^ 23162123 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 46324247) ^ 240022 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 46324247) ^ 386 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_46760033 : Nat.Prime 46760033 := by
  apply lucas_primality 46760033 (3 : ZMod 46760033)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (71, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (71, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 46760033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_71
      · exact prime_fortySixAR_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46760033) ^ 23380016 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 4250912 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 658592 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 24992 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_47855501 : Nat.Prime 47855501 := by
  apply lucas_primality 47855501 (2 : ZMod 47855501)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (11, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (11, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 47855501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47855501) ^ 23927750 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 9571100 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 6836500 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 4350500 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 423500 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_52978879 : Nat.Prime 52978879 := by
  apply lucas_primality 52978879 (3 : ZMod 52978879)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (97, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (97, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 52978879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_97
      · exact prime_fortySixAR_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52978879) ^ 26489439 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 52978879) ^ 17659626 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 52978879) ^ 2788362 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 52978879) ^ 546174 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 52978879) ^ 33174 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_54908179 : Nat.Prime 54908179 := by
  apply lucas_primality 54908179 (2 : ZMod 54908179)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (307, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (307, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) = 54908179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_307
      · exact prime_fortySixAR_2293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54908179) ^ 27454089 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 54908179) ^ 18302726 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 54908179) ^ 4223706 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 54908179) ^ 178854 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 54908179) ^ 23946 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_56041753 : Nat.Prime 56041753 := by
  apply lucas_primality 56041753 (5 : ZMod 56041753)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 56041753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56041753) ^ 28020876 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 18680584 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 4310904 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 1366872 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 166296 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_57298999 : Nat.Prime 57298999 := by
  apply lucas_primality 57298999 (3 : ZMod 57298999)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (49481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (49481, 1)] : List FactorBlock).map factorBlockValue).prod) = 57298999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_193
      · exact prime_fortySixAR_49481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57298999) ^ 28649499 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 19099666 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 296886 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 1158 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_63269953 : Nat.Prime 63269953 := by
  apply lucas_primality 63269953 (5 : ZMod 63269953)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (229, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (229, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) = 63269953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_229
      · exact prime_fortySixAR_1439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63269953) ^ 31634976 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 21089984 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 276288 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 43968 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_64998337 : Nat.Prime 64998337 := by
  apply lucas_primality 64998337 (5 : ZMod 64998337)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (26041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (26041, 1)] : List FactorBlock).map factorBlockValue).prod) = 64998337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_26041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64998337) ^ 32499168 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 21666112 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 4999872 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 2496 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_67517629 : Nat.Prime 67517629 := by
  apply lucas_primality 67517629 (6 : ZMod 67517629)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (181499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (181499, 1)] : List FactorBlock).map factorBlockValue).prod) = 67517629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_181499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 67517629) ^ 33758814 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 67517629) ^ 22505876 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 67517629) ^ 2177988 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 67517629) ^ 372 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_76415167 : Nat.Prime 76415167 := by
  apply lucas_primality 76415167 (5 : ZMod 76415167)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (593, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (593, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) = 76415167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_593
      · exact prime_fortySixAR_7159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76415167) ^ 38207583 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 76415167) ^ 25471722 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 76415167) ^ 128862 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 76415167) ^ 10674 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_76562041 : Nat.Prime 76562041 := by
  apply lucas_primality 76562041 (7 : ZMod 76562041)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (101, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (101, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 76562041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_101
      · exact prime_fortySixAR_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76562041) ^ 38281020 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 76562041) ^ 25520680 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 76562041) ^ 15312408 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 76562041) ^ 758040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 76562041) ^ 12120 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_87006637 : Nat.Prime 87006637 := by
  apply lucas_primality 87006637 (6 : ZMod 87006637)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (89513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (89513, 1)] : List FactorBlock).map factorBlockValue).prod) = 87006637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_89513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 87006637) ^ 43503318 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 87006637) ^ 29002212 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 87006637) ^ 972 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_93520067 : Nat.Prime 93520067 := by
  apply lucas_primality 93520067 (2 : ZMod 93520067)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46760033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46760033, 1)] : List FactorBlock).map factorBlockValue).prod) = 93520067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_46760033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 93520067) ^ 46760033 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 93520067) ^ 2 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_104837449 : Nat.Prime 104837449 := by
  apply lucas_primality 104837449 (7 : ZMod 104837449)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (92941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (92941, 1)] : List FactorBlock).map factorBlockValue).prod) = 104837449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_92941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 104837449) ^ 52418724 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 104837449) ^ 34945816 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 104837449) ^ 2230584 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 104837449) ^ 1128 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_113758019 : Nat.Prime 113758019 := by
  apply lucas_primality 113758019 (2 : ZMod 113758019)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (87641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (87641, 1)] : List FactorBlock).map factorBlockValue).prod) = 113758019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_87641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113758019) ^ 56879009 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 113758019) ^ 10341638 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 113758019) ^ 1928102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 113758019) ^ 1298 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_116810581 : Nat.Prime 116810581 := by
  apply lucas_primality 116810581 (2 : ZMod 116810581)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) = 116810581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_151
      · exact prime_fortySixAR_12893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116810581) ^ 58405290 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 116810581) ^ 38936860 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 116810581) ^ 23362116 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 116810581) ^ 773580 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 116810581) ^ 9060 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_127090643 : Nat.Prime 127090643 := by
  apply lucas_primality 127090643 (2 : ZMod 127090643)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9077903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9077903, 1)] : List FactorBlock).map factorBlockValue).prod) = 127090643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_9077903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 127090643) ^ 63545321 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 127090643) ^ 18155806 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 127090643) ^ 14 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_137881031 : Nat.Prime 137881031 := by
  apply lucas_primality 137881031 (7 : ZMod 137881031)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1969729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1969729, 1)] : List FactorBlock).map factorBlockValue).prod) = 137881031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_1969729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 137881031) ^ 68940515 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 27576206 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 19697290 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 70 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_142184897 : Nat.Prime 142184897 := by
  apply lucas_primality 142184897 (5 : ZMod 142184897)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (23, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (23, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) = 142184897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_13799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 142184897) ^ 71092448 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 20312128 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 6181952 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 10304 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_149921671 : Nat.Prime 149921671 := by
  apply lucas_primality 149921671 (3 : ZMod 149921671)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4997389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4997389, 1)] : List FactorBlock).map factorBlockValue).prod) = 149921671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_4997389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 149921671) ^ 74960835 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 49973890 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 29984334 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 30 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_151220149 : Nat.Prime 151220149 := by
  apply lucas_primality 151220149 (2 : ZMod 151220149)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (367, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (367, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) = 151220149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_367
      · exact prime_fortySixAR_34337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151220149) ^ 75610074 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 151220149) ^ 50406716 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 151220149) ^ 412044 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 151220149) ^ 4404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_152353283 : Nat.Prime 152353283 := by
  apply lucas_primality 152353283 (2 : ZMod 152353283)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2457311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2457311, 1)] : List FactorBlock).map factorBlockValue).prod) = 152353283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_2457311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 152353283) ^ 76176641 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 152353283) ^ 4914622 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 152353283) ^ 62 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_170365511 : Nat.Prime 170365511 := by
  apply lucas_primality 170365511 (14 : ZMod 170365511)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1087, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1087, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) = 170365511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_1087
      · exact prime_fortySixAR_2239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 170365511) ^ 85182755 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 34073102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 24337930 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 156730 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 76090 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_177900851 : Nat.Prime 177900851 := by
  apply lucas_primality 177900851 (2 : ZMod 177900851)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (197, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (197, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 177900851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_197
      · exact prime_fortySixAR_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 177900851) ^ 88950425 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 35580170 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 903050 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 9850 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_188983007 : Nat.Prime 188983007 := by
  apply lucas_primality 188983007 (5 : ZMod 188983007)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (137, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (137, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 188983007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_137
      · exact prime_fortySixAR_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 188983007) ^ 94491503 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 9946474 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 6096226 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 1379438 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 161386 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_190251689 : Nat.Prime 190251689 := by
  apply lucas_primality 190251689 (3 : ZMod 190251689)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) = 190251689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_196541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 190251689) ^ 95125844 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 190251689) ^ 17295608 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 190251689) ^ 968 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_191
      · exact prime_fortySixAR_383
      · exact prime_fortySixAR_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_252359449 : Nat.Prime 252359449 := by
  apply lucas_primality 252359449 (7 : ZMod 252359449)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (131, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (131, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) = 252359449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_131
      · exact prime_fortySixAR_7297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 252359449) ^ 126179724 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 252359449) ^ 84119816 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 252359449) ^ 22941768 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 252359449) ^ 1926408 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 252359449) ^ 34584 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_279560689 : Nat.Prime 279560689 := by
  apply lucas_primality 279560689 (13 : ZMod 279560689)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (529471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (529471, 1)] : List FactorBlock).map factorBlockValue).prod) = 279560689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_529471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 279560689) ^ 139780344 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 93186896 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 25414608 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 528 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_287645443 : Nat.Prime 287645443 := by
  apply lucas_primality 287645443 (5 : ZMod 287645443)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6848701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6848701, 1)] : List FactorBlock).map factorBlockValue).prod) = 287645443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_6848701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 287645443) ^ 143822721 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 95881814 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 41092206 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 42 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_401513269 : Nat.Prime 401513269 := by
  apply lucas_primality 401513269 (2 : ZMod 401513269)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2573803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2573803, 1)] : List FactorBlock).map factorBlockValue).prod) = 401513269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_2573803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 401513269) ^ 200756634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 133837756 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 30885636 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 156 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_419349797 : Nat.Prime 419349797 := by
  apply lucas_primality 419349797 (2 : ZMod 419349797)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (104837449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (104837449, 1)] : List FactorBlock).map factorBlockValue).prod) = 419349797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_104837449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 419349797) ^ 209674898 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 419349797) ^ 4 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_464635181 : Nat.Prime 464635181 := by
  apply lucas_primality 464635181 (2 : ZMod 464635181)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (261031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (261031, 1)] : List FactorBlock).map factorBlockValue).prod) = 464635181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_89
      · exact prime_fortySixAR_261031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 464635181) ^ 232317590 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 464635181) ^ 92927036 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 464635181) ^ 5220620 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 464635181) ^ 1780 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_495519253 : Nat.Prime 495519253 := by
  apply lucas_primality 495519253 (2 : ZMod 495519253)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (631, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (631, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) = 495519253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_631
      · exact prime_fortySixAR_2111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 495519253) ^ 247759626 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 495519253) ^ 165173084 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 495519253) ^ 15984492 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 495519253) ^ 785292 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 495519253) ^ 234732 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_509541427 : Nat.Prime 509541427 := by
  apply lucas_primality 509541427 (3 : ZMod 509541427)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (181, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (181, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) = 509541427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_181
      · exact prime_fortySixAR_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 509541427) ^ 254770713 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 509541427) ^ 169847142 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 509541427) ^ 17570394 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 509541427) ^ 2815146 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 509541427) ^ 94482 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_529552747 : Nat.Prime 529552747 := by
  apply lucas_primality 529552747 (2 : ZMod 529552747)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29419597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29419597, 1)] : List FactorBlock).map factorBlockValue).prod) = 529552747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_29419597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 529552747) ^ 264776373 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 529552747) ^ 176517582 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 529552747) ^ 18 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_540402979 : Nat.Prime 540402979 := by
  apply lucas_primality 540402979 (2 : ZMod 540402979)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (2053, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (2053, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) = 540402979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_2053
      · exact prime_fortySixAR_2309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 540402979) ^ 270201489 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 180134326 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 28442262 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 263226 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 234042 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_574463957 : Nat.Prime 574463957 := by
  apply lucas_primality 574463957 (2 : ZMod 574463957)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (41, 1), (28949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (41, 1), (28949, 1)] : List FactorBlock).map factorBlockValue).prod) = 574463957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_28949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 574463957) ^ 287231978 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 52223996 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 14011316 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 19844 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_604483333 : Nat.Prime 604483333 := by
  apply lucas_primality 604483333 (2 : ZMod 604483333)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (2190157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (2190157, 1)] : List FactorBlock).map factorBlockValue).prod) = 604483333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_2190157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 604483333) ^ 302241666 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 201494444 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 26281884 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 276 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_604694273 : Nat.Prime 604694273 := by
  apply lucas_primality 604694273 (3 : ZMod 604694273)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7, 1), (13, 1), (101, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7, 1), (13, 1), (101, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 604694273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_101
      · exact prime_fortySixAR_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 604694273) ^ 302347136 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 86384896 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 46514944 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 5987072 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 2352896 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_626571461 : Nat.Prime 626571461 := by
  apply lucas_primality 626571461 (3 : ZMod 626571461)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31328573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31328573, 1)] : List FactorBlock).map factorBlockValue).prod) = 626571461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_31328573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 626571461) ^ 313285730 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 626571461) ^ 125314292 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 626571461) ^ 20 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_649983371 : Nat.Prime 649983371 := by
  apply lucas_primality 649983371 (2 : ZMod 649983371)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (64998337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (64998337, 1)] : List FactorBlock).map factorBlockValue).prod) = 649983371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_64998337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 649983371) ^ 324991685 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 649983371) ^ 129996674 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 649983371) ^ 10 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_740970437 : Nat.Prime 740970437 := by
  apply lucas_primality 740970437 (2 : ZMod 740970437)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (263503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (263503, 1)] : List FactorBlock).map factorBlockValue).prod) = 740970437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_263503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 740970437) ^ 370485218 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 740970437) ^ 38998444 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 740970437) ^ 20026228 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 740970437) ^ 2812 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_894001609 : Nat.Prime 894001609 := by
  apply lucas_primality 894001609 (11 : ZMod 894001609)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (12416689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (12416689, 1)] : List FactorBlock).map factorBlockValue).prod) = 894001609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_12416689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 894001609) ^ 447000804 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 894001609) ^ 298000536 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 894001609) ^ 72 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_941297459 : Nat.Prime 941297459 := by
  apply lucas_primality 941297459 (2 : ZMod 941297459)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (151, 1), (27583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (151, 1), (27583, 1)] : List FactorBlock).map factorBlockValue).prod) = 941297459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_113
      · exact prime_fortySixAR_151
      · exact prime_fortySixAR_27583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 941297459) ^ 470648729 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 8330066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 6233758 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 34126 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1009161947 : Nat.Prime 1009161947 := by
  apply lucas_primality 1009161947 (2 : ZMod 1009161947)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (946681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (946681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1009161947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_946681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1009161947) ^ 504580973 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 77627842 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 24613706 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 1066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1137479177 : Nat.Prime 1137479177 := by
  apply lucas_primality 1137479177 (3 : ZMod 1137479177)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (142184897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (142184897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137479177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_142184897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1137479177) ^ 568739588 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137479177) ^ 8 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1140538079 : Nat.Prime 1140538079 := by
  apply lucas_primality 1140538079 (7 : ZMod 1140538079)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7411, 1), (76949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7411, 1), (76949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140538079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7411
      · exact prime_fortySixAR_76949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1140538079) ^ 570269039 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 1140538079) ^ 153898 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 1140538079) ^ 14822 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1157796803 : Nat.Prime 1157796803 := by
  apply lucas_primality 1157796803 (2 : ZMod 1157796803)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2851, 1), (203051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2851, 1), (203051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157796803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_2851
      · exact prime_fortySixAR_203051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1157796803) ^ 578898401 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157796803) ^ 406102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157796803) ^ 5702 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1209388547 : Nat.Prime 1209388547 := by
  apply lucas_primality 1209388547 (2 : ZMod 1209388547)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (604694273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (604694273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1209388547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_604694273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1209388547) ^ 604694273 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209388547) ^ 2 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1220738251 : Nat.Prime 1220738251 := by
  apply lucas_primality 1220738251 (2 : ZMod 1220738251)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (1627651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (1627651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1220738251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_1627651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1220738251) ^ 610369125 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 406912750 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 244147650 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 750 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_113
      · exact prime_fortySixAR_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1253142923 : Nat.Prime 1253142923 := by
  apply lucas_primality 1253142923 (2 : ZMod 1253142923)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (626571461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (626571461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1253142923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_626571461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1253142923) ^ 626571461 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1253142923) ^ 2 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1584080819 : Nat.Prime 1584080819 := by
  apply lucas_primality 1584080819 (2 : ZMod 1584080819)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (12984269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (12984269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1584080819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_61
      · exact prime_fortySixAR_12984269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1584080819) ^ 792040409 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584080819) ^ 25968538 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584080819) ^ 122 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1647245371 : Nat.Prime 1647245371 := by
  apply lucas_primality 1647245371 (3 : ZMod 1647245371)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (54908179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (54908179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1647245371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_54908179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1647245371) ^ 823622685 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1647245371) ^ 549081790 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1647245371) ^ 329449074 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1647245371) ^ 30 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1703927881 : Nat.Prime 1703927881 := by
  apply lucas_primality 1703927881 (17 : ZMod 1703927881)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (1577711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (1577711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1703927881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_1577711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1703927881) ^ 851963940 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 567975960 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 340785576 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 1080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2248342417 : Nat.Prime 2248342417 := by
  apply lucas_primality 2248342417 (5 : ZMod 2248342417)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (101, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (101, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2248342417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_101
      · exact prime_fortySixAR_154589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2248342417) ^ 1124171208 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248342417) ^ 749447472 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248342417) ^ 22260816 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248342417) ^ 14544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2413558747 : Nat.Prime 2413558747 := by
  apply lucas_primality 2413558747 (2 : ZMod 2413558747)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1741, 1), (77017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1741, 1), (77017, 1)] : List FactorBlock).map factorBlockValue).prod) = 2413558747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_1741
      · exact prime_fortySixAR_77017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2413558747) ^ 1206779373 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 804519582 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 1386306 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 31338 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2763641267 : Nat.Prime 2763641267 := by
  apply lucas_primality 2763641267 (2 : ZMod 2763641267)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (191, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (191, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) = 2763641267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_191
      · exact prime_fortySixAR_153929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2763641267) ^ 1381820633 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2763641267) ^ 58800878 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2763641267) ^ 14469326 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2763641267) ^ 17954 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2844774137 : Nat.Prime 2844774137 := by
  apply lucas_primality 2844774137 (3 : ZMod 2844774137)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (15460729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (15460729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844774137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_15460729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2844774137) ^ 1422387068 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844774137) ^ 123685832 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844774137) ^ 184 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2960967601 : Nat.Prime 2960967601 := by
  apply lucas_primality 2960967601 (52 : ZMod 2960967601)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (19, 1), (73, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (19, 1), (73, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2960967601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_73
      · exact prime_fortySixAR_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (52 : ZMod 2960967601) ^ 1480483800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 986989200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 592193520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 155840400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 40561200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 4993200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_3330424087 : Nat.Prime 3330424087 := by
  apply lucas_primality 3330424087 (7 : ZMod 3330424087)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (4587361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (4587361, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330424087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_4587361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3330424087) ^ 1665212043 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 1110141362 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 302765826 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 726 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_3746573059 : Nat.Prime 3746573059 := by
  apply lucas_primality 3746573059 (2 : ZMod 3746573059)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (14521601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (14521601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746573059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_14521601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3746573059) ^ 1873286529 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 1248857686 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 87129606 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 258 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4126546859 : Nat.Prime 4126546859 := by
  apply lucas_primality 4126546859 (2 : ZMod 4126546859)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (43, 1), (883, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (43, 1), (883, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 4126546859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_883
      · exact prime_fortySixAR_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4126546859) ^ 2063273429 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126546859) ^ 589506694 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126546859) ^ 95966206 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126546859) ^ 4673326 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126546859) ^ 3720962 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4256140153 : Nat.Prime 4256140153 := by
  apply lucas_primality 4256140153 (7 : ZMod 4256140153)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (337, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (337, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4256140153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_337
      · exact prime_fortySixAR_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4256140153) ^ 2128070076 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 1418713384 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 386921832 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 12629496 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 978648 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4951267327 : Nat.Prime 4951267327 := by
  apply lucas_primality 4951267327 (3 : ZMod 4951267327)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (641, 1), (429127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (641, 1), (429127, 1)] : List FactorBlock).map factorBlockValue).prod) = 4951267327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_641
      · exact prime_fortySixAR_429127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4951267327) ^ 2475633663 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4951267327) ^ 1650422442 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4951267327) ^ 7724286 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4951267327) ^ 11538 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_5049978421 : Nat.Prime 5049978421 := by
  apply lucas_primality 5049978421 (7 : ZMod 5049978421)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (107, 1), (139, 1), (5659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (107, 1), (139, 1), (5659, 1)] : List FactorBlock).map factorBlockValue).prod) = 5049978421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_107
      · exact prime_fortySixAR_139
      · exact prime_fortySixAR_5659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5049978421) ^ 2524989210 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 5049978421) ^ 1683326140 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 5049978421) ^ 1009995684 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 5049978421) ^ 47196060 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 5049978421) ^ 36330780 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 5049978421) ^ 892380 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_6335859269 : Nat.Prime 6335859269 := by
  apply lucas_primality 6335859269 (2 : ZMod 6335859269)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (7993, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (7993, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) = 6335859269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_7993
      · exact prime_fortySixAR_11657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6335859269) ^ 3167929634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 372697604 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 792676 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 543524 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_9397157443 : Nat.Prime 9397157443 := by
  apply lucas_primality 9397157443 (2 : ZMod 9397157443)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (157, 1), (243311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (157, 1), (243311, 1)] : List FactorBlock).map factorBlockValue).prod) = 9397157443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_157
      · exact prime_fortySixAR_243311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9397157443) ^ 4698578721 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 3132385814 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 229198962 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 59854506 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 38622 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_13028721283 : Nat.Prime 13028721283 := by
  apply lucas_primality 13028721283 (2 : ZMod 13028721283)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (9915313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (9915313, 1)] : List FactorBlock).map factorBlockValue).prod) = 13028721283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_73
      · exact prime_fortySixAR_9915313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13028721283) ^ 6514360641 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 4342907094 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 178475634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 1314 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_13187705449 : Nat.Prime 13187705449 := by
  apply lucas_primality 13187705449 (11 : ZMod 13187705449)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (677, 1), (811651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (677, 1), (811651, 1)] : List FactorBlock).map factorBlockValue).prod) = 13187705449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_677
      · exact prime_fortySixAR_811651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 13187705449) ^ 6593852724 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 4395901816 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 19479624 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 16248 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_14919349673 : Nat.Prime 14919349673 := by
  apply lucas_primality 14919349673 (3 : ZMod 14919349673)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9551, 1), (195259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9551, 1), (195259, 1)] : List FactorBlock).map factorBlockValue).prod) = 14919349673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_9551
      · exact prime_fortySixAR_195259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14919349673) ^ 7459674836 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 14919349673) ^ 1562072 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 14919349673) ^ 76408 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_15118640561 : Nat.Prime 15118640561 := by
  apply lucas_primality 15118640561 (3 : ZMod 15118640561)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (188983007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (188983007, 1)] : List FactorBlock).map factorBlockValue).prod) = 15118640561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_188983007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15118640561) ^ 7559320280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 15118640561) ^ 3023728112 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 15118640561) ^ 80 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_15443297417 : Nat.Prime 15443297417 := by
  apply lucas_primality 15443297417 (3 : ZMod 15443297417)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14887, 1), (129671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14887, 1), (129671, 1)] : List FactorBlock).map factorBlockValue).prod) = 15443297417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_14887
      · exact prime_fortySixAR_129671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15443297417) ^ 7721648708 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 15443297417) ^ 1037368 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 15443297417) ^ 119096 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_15793106327 : Nat.Prime 15793106327 := by
  apply lucas_primality 15793106327 (5 : ZMod 15793106327)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (16082593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (16082593, 1)] : List FactorBlock).map factorBlockValue).prod) = 15793106327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_491
      · exact prime_fortySixAR_16082593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15793106327) ^ 7896553163 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 15793106327) ^ 32165186 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 15793106327) ^ 982 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_17054500517 : Nat.Prime 17054500517 := by
  apply lucas_primality 17054500517 (2 : ZMod 17054500517)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1151, 1), (3704279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1151, 1), (3704279, 1)] : List FactorBlock).map factorBlockValue).prod) = 17054500517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_1151
      · exact prime_fortySixAR_3704279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17054500517) ^ 8527250258 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17054500517) ^ 14817116 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17054500517) ^ 4604 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_17779879363 : Nat.Prime 17779879363 := by
  apply lucas_primality 17779879363 (2 : ZMod 17779879363)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (83, 1), (5100367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (83, 1), (5100367, 1)] : List FactorBlock).map factorBlockValue).prod) = 17779879363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_83
      · exact prime_fortySixAR_5100367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17779879363) ^ 8889939681 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17779879363) ^ 5926626454 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17779879363) ^ 2539982766 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17779879363) ^ 214215414 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 17779879363) ^ 3486 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_25536840919 : Nat.Prime 25536840919 := by
  apply lucas_primality 25536840919 (7 : ZMod 25536840919)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4256140153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4256140153, 1)] : List FactorBlock).map factorBlockValue).prod) = 25536840919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_4256140153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 25536840919) ^ 12768420459 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 25536840919) ^ 8512280306 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 25536840919) ^ 6 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_27262846097 : Nat.Prime 27262846097 := by
  apply lucas_primality 27262846097 (3 : ZMod 27262846097)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1703927881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1703927881, 1)] : List FactorBlock).map factorBlockValue).prod) = 27262846097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_1703927881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 27262846097) ^ 13631423048 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 27262846097) ^ 16 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_32940583843 : Nat.Prime 32940583843 := by
  apply lucas_primality 32940583843 (3 : ZMod 32940583843)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (116810581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (116810581, 1)] : List FactorBlock).map factorBlockValue).prod) = 32940583843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_116810581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32940583843) ^ 16470291921 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 32940583843) ^ 10980194614 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 32940583843) ^ 700863486 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 32940583843) ^ 282 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_34312851709 : Nat.Prime 34312851709 := by
  apply lucas_primality 34312851709 (2 : ZMod 34312851709)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3023, 1), (945883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3023, 1), (945883, 1)] : List FactorBlock).map factorBlockValue).prod) = 34312851709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_3023
      · exact prime_fortySixAR_945883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34312851709) ^ 17156425854 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 34312851709) ^ 11437617236 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 34312851709) ^ 11350596 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 34312851709) ^ 36276 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_151
      · exact prime_fortySixAR_479
      · exact prime_fortySixAR_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_49518562309 : Nat.Prime 49518562309 := by
  apply lucas_primality 49518562309 (6 : ZMod 49518562309)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4126546859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4126546859, 1)] : List FactorBlock).map factorBlockValue).prod) = 49518562309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_4126546859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 49518562309) ^ 24759281154 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 49518562309) ^ 16506187436 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 49518562309) ^ 12 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_55110439577 : Nat.Prime 55110439577 := by
  apply lucas_primality 55110439577 (3 : ZMod 55110439577)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (571, 1), (12064457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (571, 1), (12064457, 1)] : List FactorBlock).map factorBlockValue).prod) = 55110439577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_571
      · exact prime_fortySixAR_12064457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55110439577) ^ 27555219788 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 55110439577) ^ 96515656 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 55110439577) ^ 4568 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_55142972383 : Nat.Prime 55142972383 := by
  apply lucas_primality 55142972383 (5 : ZMod 55142972383)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (569, 1), (16152013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (569, 1), (16152013, 1)] : List FactorBlock).map factorBlockValue).prod) = 55142972383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_569
      · exact prime_fortySixAR_16152013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55142972383) ^ 27571486191 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 55142972383) ^ 18380990794 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 55142972383) ^ 96912078 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 55142972383) ^ 3414 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_55494704549 : Nat.Prime 55494704549 := by
  apply lucas_primality 55494704549 (2 : ZMod 55494704549)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10343, 1), (1341359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10343, 1), (1341359, 1)] : List FactorBlock).map factorBlockValue).prod) = 55494704549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_10343
      · exact prime_fortySixAR_1341359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55494704549) ^ 27747352274 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 55494704549) ^ 5365436 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 55494704549) ^ 41372 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_57355267721 : Nat.Prime 57355267721 := by
  apply lucas_primality 57355267721 (3 : ZMod 57355267721)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2903, 1), (493931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2903, 1), (493931, 1)] : List FactorBlock).map factorBlockValue).prod) = 57355267721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_2903
      · exact prime_fortySixAR_493931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57355267721) ^ 28677633860 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 11471053544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 19757240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 116120 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_58538318617 : Nat.Prime 58538318617 := by
  apply lucas_primality 58538318617 (5 : ZMod 58538318617)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (67, 1), (373, 1), (32533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (67, 1), (373, 1), (32533, 1)] : List FactorBlock).map factorBlockValue).prod) = 58538318617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_67
      · exact prime_fortySixAR_373
      · exact prime_fortySixAR_32533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58538318617) ^ 29269159308 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 58538318617) ^ 19512772872 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 58538318617) ^ 873706248 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 58538318617) ^ 156939192 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 58538318617) ^ 1799352 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_71491695013 : Nat.Prime 71491695013 := by
  apply lucas_primality 71491695013 (2 : ZMod 71491695013)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (9109, 1), (72671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (9109, 1), (72671, 1)] : List FactorBlock).map factorBlockValue).prod) = 71491695013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_9109
      · exact prime_fortySixAR_72671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71491695013) ^ 35745847506 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 23830565004 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 7848468 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 983772 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_92060796097 : Nat.Prime 92060796097 := by
  apply lucas_primality 92060796097 (10 : ZMod 92060796097)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (1489, 1), (107339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (1489, 1), (107339, 1)] : List FactorBlock).map factorBlockValue).prod) = 92060796097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_1489
      · exact prime_fortySixAR_107339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 92060796097) ^ 46030398048 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 92060796097) ^ 30686932032 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 92060796097) ^ 61827264 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 92060796097) ^ 857664 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_97926671179 : Nat.Prime 97926671179 := by
  apply lucas_primality 97926671179 (3 : ZMod 97926671179)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (43, 1), (337, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (43, 1), (337, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) = 97926671179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_337
      · exact prime_fortySixAR_53633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97926671179) ^ 48963335589 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 32642223726 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 13989524454 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 2277364446 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 290583594 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 1825866 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_100271888593 : Nat.Prime 100271888593 := by
  apply lucas_primality 100271888593 (5 : ZMod 100271888593)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1033, 1), (2022263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1033, 1), (2022263, 1)] : List FactorBlock).map factorBlockValue).prod) = 100271888593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_1033
      · exact prime_fortySixAR_2022263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 100271888593) ^ 50135944296 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 100271888593) ^ 33423962864 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 100271888593) ^ 97068624 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 100271888593) ^ 49584 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_106247777549 : Nat.Prime 106247777549 := by
  apply lucas_primality 106247777549 (2 : ZMod 106247777549)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (127090643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (127090643, 1)] : List FactorBlock).map factorBlockValue).prod) = 106247777549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_127090643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106247777549) ^ 53123888774 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 9658888868 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 5591988292 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 836 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_116778303307 : Nat.Prime 116778303307 := by
  apply lucas_primality 116778303307 (3 : ZMod 116778303307)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (9221, 1), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (9221, 1), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) = 116778303307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_9221
      · exact prime_fortySixAR_100511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116778303307) ^ 58389151653 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 38926101102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 16682614758 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 12664386 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 1161846 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_133660878913 : Nat.Prime 133660878913 := by
  apply lucas_primality 133660878913 (15 : ZMod 133660878913)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (73, 1), (288979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (73, 1), (288979, 1)] : List FactorBlock).map factorBlockValue).prod) = 133660878913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_73
      · exact prime_fortySixAR_288979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 133660878913) ^ 66830439456 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 44553626304 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 12150988992 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 1830970944 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 462528 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_176510284939 : Nat.Prime 176510284939 := by
  apply lucas_primality 176510284939 (2 : ZMod 176510284939)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (167, 1), (439, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (167, 1), (439, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) = 176510284939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_167
      · exact prime_fortySixAR_439
      · exact prime_fortySixAR_10289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 176510284939) ^ 88255142469 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 58836761646 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 13577714226 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 1056947814 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 402073542 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 17155242 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_215564018827 : Nat.Prime 215564018827 := by
  apply lucas_primality 215564018827 (2 : ZMod 215564018827)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2763641267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2763641267, 1)] : List FactorBlock).map factorBlockValue).prod) = 215564018827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_2763641267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215564018827) ^ 107782009413 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 215564018827) ^ 71854672942 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 215564018827) ^ 16581847602 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 215564018827) ^ 78 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_268713929761 : Nat.Prime 268713929761 := by
  apply lucas_primality 268713929761 (17 : ZMod 268713929761)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (733, 1), (763739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (733, 1), (763739, 1)] : List FactorBlock).map factorBlockValue).prod) = 268713929761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_733
      · exact prime_fortySixAR_763739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 268713929761) ^ 134356964880 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 268713929761) ^ 89571309920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 268713929761) ^ 53742785952 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 268713929761) ^ 366594720 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 268713929761) ^ 351840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_300509206451 : Nat.Prime 300509206451 := by
  apply lucas_primality 300509206451 (6 : ZMod 300509206451)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (307, 1), (1103, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (307, 1), (1103, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) = 300509206451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_307
      · exact prime_fortySixAR_1103
      · exact prime_fortySixAR_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 300509206451) ^ 150254603225 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 300509206451) ^ 60101841290 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 300509206451) ^ 978857350 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 300509206451) ^ 272447150 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 300509206451) ^ 16931050 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_302573186033 : Nat.Prime 302573186033 := by
  apply lucas_primality 302573186033 (3 : ZMod 302573186033)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (19, 1), (76562041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (19, 1), (76562041, 1)] : List FactorBlock).map factorBlockValue).prod) = 302573186033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_76562041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 302573186033) ^ 151286593016 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 302573186033) ^ 23274860464 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 302573186033) ^ 15924904528 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 302573186033) ^ 3952 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_352736457529 : Nat.Prime 352736457529 := by
  apply lucas_primality 352736457529 (23 : ZMod 352736457529)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (17, 1), (19, 1), (500029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (17, 1), (19, 1), (500029, 1)] : List FactorBlock).map factorBlockValue).prod) = 352736457529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_500029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 352736457529) ^ 176368228764 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 117578819176 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 50390922504 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 27133573656 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 20749203384 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 18565076712 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (23 : ZMod 352736457529) ^ 705432 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_369210834673 : Nat.Prime 369210834673 := by
  apply lucas_primality 369210834673 (5 : ZMod 369210834673)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (521, 1), (14763709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (521, 1), (14763709, 1)] : List FactorBlock).map factorBlockValue).prod) = 369210834673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_521
      · exact prime_fortySixAR_14763709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 369210834673) ^ 184605417336 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 369210834673) ^ 123070278224 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 369210834673) ^ 708658032 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 369210834673) ^ 25008 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_397
      · exact prime_fortySixAR_2531
      · exact prime_fortySixAR_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_617623095907 : Nat.Prime 617623095907 := by
  apply lucas_primality 617623095907 (3 : ZMod 617623095907)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (239, 1), (47855501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (239, 1), (47855501, 1)] : List FactorBlock).map factorBlockValue).prod) = 617623095907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_239
      · exact prime_fortySixAR_47855501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 617623095907) ^ 308811547953 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 205874365302 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 2584197054 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 12906 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_766105227571 : Nat.Prime 766105227571 := by
  apply lucas_primality 766105227571 (3 : ZMod 766105227571)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (25536840919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (25536840919, 1)] : List FactorBlock).map factorBlockValue).prod) = 766105227571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_25536840919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 766105227571) ^ 383052613785 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 255368409190 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 153221045514 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 30 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_776925863687 : Nat.Prime 776925863687 := by
  apply lucas_primality 776925863687 (7 : ZMod 776925863687)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (55494704549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (55494704549, 1)] : List FactorBlock).map factorBlockValue).prod) = 776925863687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_55494704549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 776925863687) ^ 388462931843 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 776925863687) ^ 110989409098 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 776925863687) ^ 14 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_840939634417 : Nat.Prime 840939634417 := by
  apply lucas_primality 840939634417 (10 : ZMod 840939634417)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (23369, 1), (107099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (23369, 1), (107099, 1)] : List FactorBlock).map factorBlockValue).prod) = 840939634417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_23369
      · exact prime_fortySixAR_107099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 840939634417) ^ 420469817208 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 280313211472 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 120134233488 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 35985264 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 7851984 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1026385466377 : Nat.Prime 1026385466377 := by
  apply lucas_primality 1026385466377 (5 : ZMod 1026385466377)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (163, 1), (257, 1), (53731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (163, 1), (257, 1), (53731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026385466377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_163
      · exact prime_fortySixAR_257
      · exact prime_fortySixAR_53731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1026385466377) ^ 513192733188 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 342128488792 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 54020287704 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 6296843352 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 3993717768 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 19102296 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1034797634261 : Nat.Prime 1034797634261 := by
  apply lucas_primality 1034797634261 (2 : ZMod 1034797634261)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (587, 1), (6780223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (587, 1), (6780223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1034797634261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_587
      · exact prime_fortySixAR_6780223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1034797634261) ^ 517398817130 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034797634261) ^ 206959526852 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034797634261) ^ 79599818020 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034797634261) ^ 1762857980 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034797634261) ^ 152620 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1204531986989 : Nat.Prime 1204531986989 := by
  apply lucas_primality 1204531986989 (2 : ZMod 1204531986989)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (827, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (827, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1204531986989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_827
      · exact prime_fortySixAR_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1204531986989) ^ 602265993494 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 109502907908 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 70854822764 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 52370955956 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 38855870548 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 1456507844 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 441058948 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_35279
      · exact prime_fortySixAR_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1602309601687 : Nat.Prime 1602309601687 := by
  apply lucas_primality 1602309601687 (3 : ZMod 1602309601687)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1061, 1), (1259, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1061, 1), (1259, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1602309601687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_1061
      · exact prime_fortySixAR_1259
      · exact prime_fortySixAR_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1602309601687) ^ 801154800843 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 534103200562 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 51687406506 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 1510188126 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 1272684354 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 248458614 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2756990764841 : Nat.Prime 2756990764841 := by
  apply lucas_primality 2756990764841 (3 : ZMod 2756990764841)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (557, 1), (9518681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (557, 1), (9518681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2756990764841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_557
      · exact prime_fortySixAR_9518681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2756990764841) ^ 1378495382420 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 551398152968 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 212076212680 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 4949714120 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 289640 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_3895148684197 : Nat.Prime 3895148684197 := by
  apply lucas_primality 3895148684197 (5 : ZMod 3895148684197)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (19, 1), (4350391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (19, 1), (4350391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3895148684197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_4350391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3895148684197) ^ 1947574342098 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 1298382894732 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 556449812028 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 354104425836 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 229126393188 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 205007825484 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 895356 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4018917173657 : Nat.Prime 4018917173657 := by
  apply lucas_primality 4018917173657 (3 : ZMod 4018917173657)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (17, 1), (9413, 1), (40771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (17, 1), (9413, 1), (40771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018917173657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_9413
      · exact prime_fortySixAR_40771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4018917173657) ^ 2009458586828 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 574131024808 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 365356106696 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 236406892568 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 426953912 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 98572936 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4425375475177 : Nat.Prime 4425375475177 := by
  apply lucas_primality 4425375475177 (11 : ZMod 4425375475177)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2731, 1), (67517629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2731, 1), (67517629, 1)] : List FactorBlock).map factorBlockValue).prod) = 4425375475177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_2731
      · exact prime_fortySixAR_67517629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4425375475177) ^ 2212687737588 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 4425375475177) ^ 1475125158392 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 4425375475177) ^ 1620423096 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 4425375475177) ^ 65544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4866986602697 : Nat.Prime 4866986602697 := by
  apply lucas_primality 4866986602697 (3 : ZMod 4866986602697)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73, 1), (1871, 1), (4454239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73, 1), (1871, 1), (4454239, 1)] : List FactorBlock).map factorBlockValue).prod) = 4866986602697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_73
      · exact prime_fortySixAR_1871
      · exact prime_fortySixAR_4454239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4866986602697) ^ 2433493301348 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4866986602697) ^ 66671049352 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4866986602697) ^ 2601275576 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4866986602697) ^ 1092664 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4911242276933 : Nat.Prime 4911242276933 := by
  apply lucas_primality 4911242276933 (2 : ZMod 4911242276933)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (6977, 1), (9262091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (6977, 1), (9262091, 1)] : List FactorBlock).map factorBlockValue).prod) = 4911242276933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_6977
      · exact prime_fortySixAR_9262091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4911242276933) ^ 2455621138466 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911242276933) ^ 258486435628 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911242276933) ^ 703918916 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911242276933) ^ 530252 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_6614481846563 : Nat.Prime 6614481846563 := by
  apply lucas_primality 6614481846563 (2 : ZMod 6614481846563)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57719, 1), (57298999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57719, 1), (57298999, 1)] : List FactorBlock).map factorBlockValue).prod) = 6614481846563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_57719
      · exact prime_fortySixAR_57298999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6614481846563) ^ 3307240923281 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614481846563) ^ 114597998 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614481846563) ^ 115438 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_7256947469281 : Nat.Prime 7256947469281 := by
  apply lucas_primality 7256947469281 (14 : ZMod 7256947469281)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (15118640561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (15118640561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7256947469281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_15118640561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 7256947469281) ^ 3628473734640 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 2418982489760 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 1451389493856 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_7538507136859 : Nat.Prime 7538507136859 := by
  apply lucas_primality 7538507136859 (2 : ZMod 7538507136859)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1933, 1), (649983371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1933, 1), (649983371, 1)] : List FactorBlock).map factorBlockValue).prod) = 7538507136859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_1933
      · exact prime_fortySixAR_649983371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7538507136859) ^ 3769253568429 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 2512835712286 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 3899900226 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 11598 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_8322364437809 : Nat.Prime 8322364437809 := by
  apply lucas_primality 8322364437809 (3 : ZMod 8322364437809)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (5049978421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (5049978421, 1)] : List FactorBlock).map factorBlockValue).prod) = 8322364437809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_103
      · exact prime_fortySixAR_5049978421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8322364437809) ^ 4161182218904 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 8322364437809) ^ 80799654736 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 8322364437809) ^ 1648 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_9111438852413 : Nat.Prime 9111438852413 := by
  apply lucas_primality 9111438852413 (3 : ZMod 9111438852413)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2293, 1), (76415167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2293, 1), (76415167, 1)] : List FactorBlock).map factorBlockValue).prod) = 9111438852413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_2293
      · exact prime_fortySixAR_76415167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9111438852413) ^ 4555719426206 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 9111438852413) ^ 700879911724 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 9111438852413) ^ 3973588684 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 9111438852413) ^ 119236 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_9225270165289 : Nat.Prime 9225270165289 := by
  apply lucas_primality 9225270165289 (7 : ZMod 9225270165289)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (574913, 1), (668599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (574913, 1), (668599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9225270165289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_574913
      · exact prime_fortySixAR_668599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9225270165289) ^ 4612635082644 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 3075090055096 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 16046376 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 13797912 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_9676884376009 : Nat.Prime 9676884376009 := by
  apply lucas_primality 9676884376009 (17 : ZMod 9676884376009)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5077, 1), (26472557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5077, 1), (26472557, 1)] : List FactorBlock).map factorBlockValue).prod) = 9676884376009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5077
      · exact prime_fortySixAR_26472557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 9676884376009) ^ 4838442188004 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 9676884376009) ^ 3225628125336 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 9676884376009) ^ 1906024104 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 9676884376009) ^ 365544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11003914253261 : Nat.Prime 11003914253261 := by
  apply lucas_primality 11003914253261 (3 : ZMod 11003914253261)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1451, 1), (6311, 1), (60083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1451, 1), (6311, 1), (60083, 1)] : List FactorBlock).map factorBlockValue).prod) = 11003914253261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_1451
      · exact prime_fortySixAR_6311
      · exact prime_fortySixAR_60083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11003914253261) ^ 5501957126630 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 2200782850652 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 7583676260 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 1743608660 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 183145220 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11939588383213 : Nat.Prime 11939588383213 := by
  apply lucas_primality 11939588383213 (14 : ZMod 11939588383213)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (15793106327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (15793106327, 1)] : List FactorBlock).map factorBlockValue).prod) = 11939588383213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_15793106327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 11939588383213) ^ 5969794191606 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 11939588383213) ^ 3979862794404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 11939588383213) ^ 1705655483316 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 11939588383213) ^ 756 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_13455034150673 : Nat.Prime 13455034150673 := by
  apply lucas_primality 13455034150673 (3 : ZMod 13455034150673)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (840939634417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (840939634417, 1)] : List FactorBlock).map factorBlockValue).prod) = 13455034150673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_840939634417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13455034150673) ^ 6727517075336 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 13455034150673) ^ 16 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_13938717533443 : Nat.Prime 13938717533443 := by
  apply lucas_primality 13938717533443 (2 : ZMod 13938717533443)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (61, 1), (12841, 1), (228139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (61, 1), (12841, 1), (228139, 1)] : List FactorBlock).map factorBlockValue).prod) = 13938717533443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_61
      · exact prime_fortySixAR_12841
      · exact prime_fortySixAR_228139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13938717533443) ^ 6969358766721 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 4646239177814 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 1072209041034 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 228503566122 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 1085485362 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 61097478 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_16027271091163 : Nat.Prime 16027271091163 := by
  apply lucas_primality 16027271091163 (2 : ZMod 16027271091163)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (491, 1), (604483333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (491, 1), (604483333, 1)] : List FactorBlock).map factorBlockValue).prod) = 16027271091163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_491
      · exact prime_fortySixAR_604483333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16027271091163) ^ 8013635545581 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 5342423697054 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 32642099982 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 26514 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_16116755127691 : Nat.Prime 16116755127691 := by
  apply lucas_primality 16116755127691 (3 : ZMod 16116755127691)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1213, 1), (63269953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1213, 1), (63269953, 1)] : List FactorBlock).map factorBlockValue).prod) = 16116755127691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_1213
      · exact prime_fortySixAR_63269953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16116755127691) ^ 8058377563845 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 5372251709230 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 3223351025538 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 2302393589670 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 13286690130 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 254730 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_17674707654223 : Nat.Prime 17674707654223 := by
  apply lucas_primality 17674707654223 (6 : ZMod 17674707654223)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (55603, 1), (52978879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (55603, 1), (52978879, 1)] : List FactorBlock).map factorBlockValue).prod) = 17674707654223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_55603
      · exact prime_fortySixAR_52978879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17674707654223) ^ 8837353827111 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 17674707654223) ^ 5891569218074 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 17674707654223) ^ 317873274 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 17674707654223) ^ 333618 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_27648080720861 : Nat.Prime 27648080720861 := by
  apply lucas_primality 27648080720861 (2 : ZMod 27648080720861)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (709, 1), (3011, 1), (647557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (709, 1), (3011, 1), (647557, 1)] : List FactorBlock).map factorBlockValue).prod) = 27648080720861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_709
      · exact prime_fortySixAR_3011
      · exact prime_fortySixAR_647557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27648080720861) ^ 13824040360430 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 5529616144172 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 38995882540 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 9182358260 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 42695980 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_52332132488113 : Nat.Prime 52332132488113 := by
  apply lucas_primality 52332132488113 (5 : ZMod 52332132488113)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (97, 1), (3746573059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (97, 1), (3746573059, 1)] : List FactorBlock).map factorBlockValue).prod) = 52332132488113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_97
      · exact prime_fortySixAR_3746573059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52332132488113) ^ 26166066244056 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 17444044162704 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 539506520496 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 13968 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_66128352046711 : Nat.Prime 66128352046711 := by
  apply lucas_primality 66128352046711 (6 : ZMod 66128352046711)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1759, 1), (1253142923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1759, 1), (1253142923, 1)] : List FactorBlock).map factorBlockValue).prod) = 66128352046711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_1759
      · exact prime_fortySixAR_1253142923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 66128352046711) ^ 33064176023355 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 66128352046711) ^ 22042784015570 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 66128352046711) ^ 13225670409342 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 66128352046711) ^ 37594287690 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 66128352046711) ^ 52770 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_79656758553187 : Nat.Prime 79656758553187 := by
  apply lucas_primality 79656758553187 (2 : ZMod 79656758553187)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4425375475177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4425375475177, 1)] : List FactorBlock).map factorBlockValue).prod) = 79656758553187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_4425375475177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79656758553187) ^ 39828379276593 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 79656758553187) ^ 26552252851062 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 79656758553187) ^ 18 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_94256492157427 : Nat.Prime 94256492157427 := by
  apply lucas_primality 94256492157427 (2 : ZMod 94256492157427)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (176510284939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (176510284939, 1)] : List FactorBlock).map factorBlockValue).prod) = 94256492157427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_89
      · exact prime_fortySixAR_176510284939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94256492157427) ^ 47128246078713 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 31418830719142 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 1059061709634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 534 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_107556384046561 : Nat.Prime 107556384046561 := by
  apply lucas_primality 107556384046561 (13 : ZMod 107556384046561)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (19, 1), (41, 1), (287645443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (19, 1), (41, 1), (287645443, 1)] : List FactorBlock).map factorBlockValue).prod) = 107556384046561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_287645443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 107556384046561) ^ 53778192023280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 35852128015520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 21511276809312 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 5660862318240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 2623326440160 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 373920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_135548253744649 : Nat.Prime 135548253744649 := by
  apply lucas_primality 135548253744649 (13 : ZMod 135548253744649)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (71491695013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (71491695013, 1)] : List FactorBlock).map factorBlockValue).prod) = 135548253744649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_79
      · exact prime_fortySixAR_71491695013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 135548253744649) ^ 67774126872324 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 45182751248216 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 1715800680312 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 1896 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_175908624084631 : Nat.Prime 175908624084631 := by
  apply lucas_primality 175908624084631 (6 : ZMod 175908624084631)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (12829, 1), (152353283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (12829, 1), (152353283, 1)] : List FactorBlock).map factorBlockValue).prod) = 175908624084631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_12829
      · exact prime_fortySixAR_152353283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 175908624084631) ^ 87954312042315 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 175908624084631) ^ 58636208028210 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 175908624084631) ^ 35181724816926 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 175908624084631) ^ 13711795470 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 175908624084631) ^ 1154610 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_196741102020989 : Nat.Prime 196741102020989 := by
  apply lucas_primality 196741102020989 (2 : ZMod 196741102020989)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1109, 1), (6335859269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1109, 1), (6335859269, 1)] : List FactorBlock).map factorBlockValue).prod) = 196741102020989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_1109
      · exact prime_fortySixAR_6335859269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 196741102020989) ^ 98370551010494 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 28105871717284 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 177404059532 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 31052 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_209328529952453 : Nat.Prime 209328529952453 := by
  apply lucas_primality 209328529952453 (2 : ZMod 209328529952453)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52332132488113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52332132488113, 1)] : List FactorBlock).map factorBlockValue).prod) = 209328529952453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_52332132488113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 209328529952453) ^ 104664264976226 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 209328529952453) ^ 4 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_242026467870289 : Nat.Prime 242026467870289 := by
  apply lucas_primality 242026467870289 (13 : ZMod 242026467870289)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3061, 1), (1647245371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3061, 1), (1647245371, 1)] : List FactorBlock).map factorBlockValue).prod) = 242026467870289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_3061
      · exact prime_fortySixAR_1647245371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 242026467870289) ^ 121013233935144 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 242026467870289) ^ 80675489290096 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 242026467870289) ^ 79067777808 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 242026467870289) ^ 146928 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_334529220802633 : Nat.Prime 334529220802633 := by
  apply lucas_primality 334529220802633 (5 : ZMod 334529220802633)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13938717533443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13938717533443, 1)] : List FactorBlock).map factorBlockValue).prod) = 334529220802633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13938717533443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 334529220802633) ^ 167264610401316 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 334529220802633) ^ 111509740267544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 334529220802633) ^ 24 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_380053619276029 : Nat.Prime 380053619276029 := by
  apply lucas_primality 380053619276029 (6 : ZMod 380053619276029)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229699, 1), (137881031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229699, 1), (137881031, 1)] : List FactorBlock).map factorBlockValue).prod) = 380053619276029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_229699
      · exact prime_fortySixAR_137881031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 380053619276029) ^ 190026809638014 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 126684539758676 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 1654572372 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 2756388 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_424812753190333 : Nat.Prime 424812753190333 := by
  apply lucas_primality 424812753190333 (2 : ZMod 424812753190333)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (302573186033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (302573186033, 1)] : List FactorBlock).map factorBlockValue).prod) = 424812753190333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_302573186033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 424812753190333) ^ 212406376595166 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 424812753190333) ^ 141604251063444 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 424812753190333) ^ 32677904091564 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 424812753190333) ^ 1404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_480079811164273 : Nat.Prime 480079811164273 := by
  apply lucas_primality 480079811164273 (5 : ZMod 480079811164273)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (17, 1), (101, 1), (529552747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (17, 1), (101, 1), (529552747, 1)] : List FactorBlock).map factorBlockValue).prod) = 480079811164273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_101
      · exact prime_fortySixAR_529552747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 480079811164273) ^ 240039905582136 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 480079811164273) ^ 160026603721424 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 480079811164273) ^ 43643619196752 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 480079811164273) ^ 28239988892016 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 480079811164273) ^ 4753265457072 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 480079811164273) ^ 906576 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_505587745966579 : Nat.Prime 505587745966579 := by
  apply lucas_primality 505587745966579 (14 : ZMod 505587745966579)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (59, 1), (167, 1), (1373, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (59, 1), (167, 1), (1373, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) = 505587745966579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_167
      · exact prime_fortySixAR_1373
      · exact prime_fortySixAR_29803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 505587745966579) ^ 252793872983289 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 168529248655526 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 45962522360598 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 26609881366662 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 8569283829942 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 3027471532734 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 368235794586 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 505587745966579) ^ 16964323926 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_520826605545199 : Nat.Prime 520826605545199 := by
  apply lucas_primality 520826605545199 (3 : ZMod 520826605545199)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (43, 1), (106247777549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (43, 1), (106247777549, 1)] : List FactorBlock).map factorBlockValue).prod) = 520826605545199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_106247777549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 520826605545199) ^ 260413302772599 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 173608868515066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 27411926607642 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 12112246640586 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 4902 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_529541254218107 : Nat.Prime 529541254218107 := by
  apply lucas_primality 529541254218107 (2 : ZMod 529541254218107)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (645179, 1), (2428303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (645179, 1), (2428303, 1)] : List FactorBlock).map factorBlockValue).prod) = 529541254218107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_645179
      · exact prime_fortySixAR_2428303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 529541254218107) ^ 264770627109053 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 529541254218107) ^ 40733942632162 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 529541254218107) ^ 820766414 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 529541254218107) ^ 218070502 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_644995937440229 : Nat.Prime 644995937440229 := by
  apply lucas_primality 644995937440229 (2 : ZMod 644995937440229)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (1209388547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (1209388547, 1)] : List FactorBlock).map factorBlockValue).prod) = 644995937440229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_1209388547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 644995937440229) ^ 322497968720114 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 58635994312748 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 37940937496484 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 28043301627836 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 20806320562588 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 533324 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_646534342540169 : Nat.Prime 646534342540169 := by
  apply lucas_primality 646534342540169 (3 : ZMod 646534342540169)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (353, 1), (179383, 1), (1276279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (353, 1), (179383, 1), (1276279, 1)] : List FactorBlock).map factorBlockValue).prod) = 646534342540169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_353
      · exact prime_fortySixAR_179383
      · exact prime_fortySixAR_1276279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 646534342540169) ^ 323267171270084 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 646534342540169) ^ 1831542046856 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 646534342540169) ^ 3604211896 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 646534342540169) ^ 506577592 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_792963000799919 : Nat.Prime 792963000799919 := by
  apply lucas_primality 792963000799919 (11 : ZMod 792963000799919)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (739, 1), (103333, 1), (399389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (739, 1), (103333, 1), (399389, 1)] : List FactorBlock).map factorBlockValue).prod) = 792963000799919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_739
      · exact prime_fortySixAR_103333
      · exact prime_fortySixAR_399389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 792963000799919) ^ 396481500399959 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 60997153907686 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 1073021651962 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 7673860246 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 1985440262 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_902592108976603 : Nat.Prime 902592108976603 := by
  apply lucas_primality 902592108976603 (3 : ZMod 902592108976603)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (1069, 1), (14419, 1), (80657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (1069, 1), (14419, 1), (80657, 1)] : List FactorBlock).map factorBlockValue).prod) = 902592108976603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_1069
      · exact prime_fortySixAR_14419
      · exact prime_fortySixAR_80657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 902592108976603) ^ 451296054488301 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 902592108976603) ^ 300864036325534 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 902592108976603) ^ 82053828088782 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 902592108976603) ^ 844333123458 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 902592108976603) ^ 62597413758 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 902592108976603) ^ 11190499386 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1250088974921609 : Nat.Prime 1250088974921609 := by
  apply lucas_primality 1250088974921609 (3 : ZMod 1250088974921609)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (41, 1), (13187705449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (41, 1), (13187705449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1250088974921609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_13187705449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1250088974921609) ^ 625044487460804 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 73534645583624 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 30489974998088 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 94792 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1520214477104117 : Nat.Prime 1520214477104117 := by
  apply lucas_primality 1520214477104117 (2 : ZMod 1520214477104117)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (380053619276029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (380053619276029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1520214477104117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_380053619276029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1520214477104117) ^ 760107238552058 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1520214477104117) ^ 4 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1530024826764883 : Nat.Prime 1530024826764883 := by
  apply lucas_primality 1530024826764883 (2 : ZMod 1530024826764883)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (431, 1), (72227, 1), (1170233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (431, 1), (72227, 1), (1170233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530024826764883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_431
      · exact prime_fortySixAR_72227
      · exact prime_fortySixAR_1170233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1530024826764883) ^ 765012413382441 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 510008275588294 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 218574975252126 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 3549941593422 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 21183557766 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 1307453154 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1585926001599839 : Nat.Prime 1585926001599839 := by
  apply lucas_primality 1585926001599839 (7 : ZMod 1585926001599839)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (792963000799919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (792963000799919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585926001599839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_792963000799919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 1585926001599839) ^ 792963000799919 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585926001599839) ^ 2 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2754375428293847 : Nat.Prime 2754375428293847 := by
  apply lucas_primality 2754375428293847 (5 : ZMod 2754375428293847)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (196741102020989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (196741102020989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754375428293847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_196741102020989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2754375428293847) ^ 1377187714146923 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2754375428293847) ^ 393482204041978 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2754375428293847) ^ 14 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_3176397018450847 : Nat.Prime 3176397018450847 := by
  apply lucas_primality 3176397018450847 (5 : ZMod 3176397018450847)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (61, 1), (1459, 1), (24478913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (61, 1), (1459, 1), (24478913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3176397018450847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_61
      · exact prime_fortySixAR_1459
      · exact prime_fortySixAR_24478913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3176397018450847) ^ 1588198509225423 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3176397018450847) ^ 1058799006150282 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3176397018450847) ^ 52072082269686 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3176397018450847) ^ 2177105564394 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 3176397018450847) ^ 129760542 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4858266148135991 : Nat.Prime 4858266148135991 := by
  apply lucas_primality 4858266148135991 (13 : ZMod 4858266148135991)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9811, 1), (49518562309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9811, 1), (49518562309, 1)] : List FactorBlock).map factorBlockValue).prod) = 4858266148135991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_9811
      · exact prime_fortySixAR_49518562309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4858266148135991) ^ 2429133074067995 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 4858266148135991) ^ 971653229627198 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 4858266148135991) ^ 495185623090 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 4858266148135991) ^ 98110 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_5606032292852851 : Nat.Prime 5606032292852851 := by
  apply lucas_primality 5606032292852851 (3 : ZMod 5606032292852851)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (31, 1), (811, 1), (495519253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (31, 1), (811, 1), (495519253, 1)] : List FactorBlock).map factorBlockValue).prod) = 5606032292852851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_811
      · exact prime_fortySixAR_495519253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5606032292852851) ^ 2803016146426425 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 5606032292852851) ^ 1868677430950950 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 5606032292852851) ^ 1121206458570570 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 5606032292852851) ^ 180839751382350 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 5606032292852851) ^ 6912493579350 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 5606032292852851) ^ 11313450 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_8444325085557391 : Nat.Prime 8444325085557391 := by
  apply lucas_primality 8444325085557391 (6 : ZMod 8444325085557391)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (29, 1), (36599, 1), (9822289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (29, 1), (36599, 1), (9822289, 1)] : List FactorBlock).map factorBlockValue).prod) = 8444325085557391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_36599
      · exact prime_fortySixAR_9822289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8444325085557391) ^ 4222162542778695 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8444325085557391) ^ 2814775028519130 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8444325085557391) ^ 1688865017111478 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8444325085557391) ^ 291183623639910 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8444325085557391) ^ 230725568610 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8444325085557391) ^ 859710510 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_10168483172098039 : Nat.Prime 10168483172098039 := by
  apply lucas_primality 10168483172098039 (6 : ZMod 10168483172098039)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (449, 1), (92060796097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (449, 1), (92060796097, 1)] : List FactorBlock).map factorBlockValue).prod) = 10168483172098039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_449
      · exact prime_fortySixAR_92060796097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10168483172098039) ^ 5084241586049019 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 10168483172098039) ^ 3389494390699346 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 10168483172098039) ^ 248011784685318 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 10168483172098039) ^ 22646955839862 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 10168483172098039) ^ 110454 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11041356593572759 : Nat.Prime 11041356593572759 := by
  apply lucas_primality 11041356593572759 (3 : ZMod 11041356593572759)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (47, 1), (352736457529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (47, 1), (352736457529, 1)] : List FactorBlock).map factorBlockValue).prod) = 11041356593572759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_352736457529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11041356593572759) ^ 5520678296786379 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11041356593572759) ^ 3680452197857586 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11041356593572759) ^ 298415043069534 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11041356593572759) ^ 234922480714314 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 11041356593572759) ^ 31302 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11073425744879363 : Nat.Prime 11073425744879363 := by
  apply lucas_primality 11073425744879363 (2 : ZMod 11073425744879363)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55217, 1), (100271888593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55217, 1), (100271888593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11073425744879363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_55217
      · exact prime_fortySixAR_100271888593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11073425744879363) ^ 5536712872439681 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 11073425744879363) ^ 200543777186 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 11073425744879363) ^ 110434 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_12987266597964433 : Nat.Prime 12987266597964433 := by
  apply lucas_primality 12987266597964433 (5 : ZMod 12987266597964433)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (41, 1), (1879, 1), (2143, 1), (546289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (41, 1), (1879, 1), (2143, 1), (546289, 1)] : List FactorBlock).map factorBlockValue).prod) = 12987266597964433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_1879
      · exact prime_fortySixAR_2143
      · exact prime_fortySixAR_546289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12987266597964433) ^ 6493633298982216 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 4329088865988144 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 316762599950352 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 6911797018608 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 6060320391024 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 23773619088 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_27203116748121701 : Nat.Prime 27203116748121701 := by
  apply lucas_primality 27203116748121701 (2 : ZMod 27203116748121701)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (1987, 1), (65119, 1), (67819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (1987, 1), (65119, 1), (67819, 1)] : List FactorBlock).map factorBlockValue).prod) = 27203116748121701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_1987
      · exact prime_fortySixAR_65119
      · exact prime_fortySixAR_67819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27203116748121701) ^ 13601558374060850 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27203116748121701) ^ 5440623349624340 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27203116748121701) ^ 877519895100700 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27203116748121701) ^ 13690546929100 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27203116748121701) ^ 417744694300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 27203116748121701) ^ 401113504300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_33566862285208493 : Nat.Prime 33566862285208493 := by
  apply lucas_primality 33566862285208493 (2 : ZMod 33566862285208493)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1019, 1), (32633, 1), (252359449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1019, 1), (32633, 1), (252359449, 1)] : List FactorBlock).map factorBlockValue).prod) = 33566862285208493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_1019
      · exact prime_fortySixAR_32633
      · exact prime_fortySixAR_252359449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33566862285208493) ^ 16783431142604246 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 33566862285208493) ^ 32940983596868 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 33566862285208493) ^ 1028617114124 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 33566862285208493) ^ 133012108 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_35406595722469723 : Nat.Prime 35406595722469723 := by
  apply lucas_primality 35406595722469723 (3 : ZMod 35406595722469723)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (269, 1), (300509206451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (269, 1), (300509206451, 1)] : List FactorBlock).map factorBlockValue).prod) = 35406595722469723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_73
      · exact prime_fortySixAR_269
      · exact prime_fortySixAR_300509206451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35406595722469723) ^ 17703297861234861 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 35406595722469723) ^ 11802198574156574 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 35406595722469723) ^ 485021859211914 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 35406595722469723) ^ 131623032425538 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 35406595722469723) ^ 117822 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_44856927592740961 : Nat.Prime 44856927592740961 := by
  apply lucas_primality 44856927592740961 (14 : ZMod 44856927592740961)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (29, 1), (4349, 1), (740970437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (29, 1), (4349, 1), (740970437, 1)] : List FactorBlock).map factorBlockValue).prod) = 44856927592740961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_4349
      · exact prime_fortySixAR_740970437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 44856927592740961) ^ 22428463796370480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 44856927592740961) ^ 14952309197580320 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 44856927592740961) ^ 8971385518548192 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 44856927592740961) ^ 1546790606646240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 44856927592740961) ^ 10314308483040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (14 : ZMod 44856927592740961) ^ 60538080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_49361916749518223 : Nat.Prime 49361916749518223 := by
  apply lucas_primality 49361916749518223 (5 : ZMod 49361916749518223)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (61, 1), (1034797634261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (61, 1), (1034797634261, 1)] : List FactorBlock).map factorBlockValue).prod) = 49361916749518223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_61
      · exact prime_fortySixAR_1034797634261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49361916749518223) ^ 24680958374759111 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 49361916749518223) ^ 2903642161736366 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 49361916749518223) ^ 2146170293457314 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 49361916749518223) ^ 809211749992102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 49361916749518223) ^ 47702 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_52140387579957851 : Nat.Prime 52140387579957851 := by
  apply lucas_primality 52140387579957851 (2 : ZMod 52140387579957851)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (59, 1), (17674707654223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (59, 1), (17674707654223, 1)] : List FactorBlock).map factorBlockValue).prod) = 52140387579957851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_17674707654223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52140387579957851) ^ 26070193789978925 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 52140387579957851) ^ 10428077515991570 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 52140387579957851) ^ 883735382711150 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 52140387579957851) ^ 2950 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_52723584966097631 : Nat.Prime 52723584966097631 := by
  apply lucas_primality 52723584966097631 (11 : ZMod 52723584966097631)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (4661323, 1), (87006637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (4661323, 1), (87006637, 1)] : List FactorBlock).map factorBlockValue).prod) = 52723584966097631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_4661323
      · exact prime_fortySixAR_87006637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 52723584966097631) ^ 26361792483048815 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 10544716993219526 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 4055660382007510 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 11310862810 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 605971990 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_54406233496243403 : Nat.Prime 54406233496243403 := by
  apply lucas_primality 54406233496243403 (2 : ZMod 54406233496243403)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27203116748121701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27203116748121701, 1)] : List FactorBlock).map factorBlockValue).prod) = 54406233496243403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_27203116748121701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 54406233496243403) ^ 27203116748121701 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 54406233496243403) ^ 2 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_64441731532011377 : Nat.Prime 64441731532011377 := by
  apply lucas_primality 64441731532011377 (3 : ZMod 64441731532011377)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (1097, 1), (34312851709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (1097, 1), (34312851709, 1)] : List FactorBlock).map factorBlockValue).prod) = 64441731532011377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_107
      · exact prime_fortySixAR_1097
      · exact prime_fortySixAR_34312851709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64441731532011377) ^ 32220865766005688 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 64441731532011377) ^ 602259173196368 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 64441731532011377) ^ 58743602125808 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 64441731532011377) ^ 1878064 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_64792065289942223 : Nat.Prime 64792065289942223 := by
  apply lucas_primality 64792065289942223 (5 : ZMod 64792065289942223)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (135548253744649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (135548253744649, 1)] : List FactorBlock).map factorBlockValue).prod) = 64792065289942223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_239
      · exact prime_fortySixAR_135548253744649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64792065289942223) ^ 32396032644971111 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 64792065289942223) ^ 271096507489298 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 64792065289942223) ^ 478 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_102955693875907123 : Nat.Prime 102955693875907123 := by
  apply lucas_primality 102955693875907123 (3 : ZMod 102955693875907123)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (622603, 1), (540402979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (622603, 1), (540402979, 1)] : List FactorBlock).map factorBlockValue).prod) = 102955693875907123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_622603
      · exact prime_fortySixAR_540402979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102955693875907123) ^ 51477846937953561 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 34318564625302374 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 6056217286818066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 165363311574 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 190516518 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_270328603841520479 : Nat.Prime 270328603841520479 := by
  apply lucas_primality 270328603841520479 (13 : ZMod 270328603841520479)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9679, 1), (149323, 1), (93520067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9679, 1), (149323, 1), (93520067, 1)] : List FactorBlock).map factorBlockValue).prod) = 270328603841520479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_9679
      · exact prime_fortySixAR_149323
      · exact prime_fortySixAR_93520067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 270328603841520479) ^ 135164301920760239 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 27929393929282 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 1810361456986 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 2890594634 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_281004545474211721 : Nat.Prime 281004545474211721 := by
  apply lucas_primality 281004545474211721 (11 : ZMod 281004545474211721)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (334529220802633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (334529220802633, 1)] : List FactorBlock).map factorBlockValue).prod) = 281004545474211721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_334529220802633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 281004545474211721) ^ 140502272737105860 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 93668181824737240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 56200909094842344 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 40143506496315960 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_388752391739653339 : Nat.Prime 388752391739653339 := by
  apply lucas_primality 388752391739653339 (2 : ZMod 388752391739653339)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (64792065289942223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (64792065289942223, 1)] : List FactorBlock).map factorBlockValue).prod) = 388752391739653339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_64792065289942223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 388752391739653339) ^ 194376195869826669 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 388752391739653339) ^ 129584130579884446 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 388752391739653339) ^ 6 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_472885107901000957 : Nat.Prime 472885107901000957 := by
  apply lucas_primality 472885107901000957 (2 : ZMod 472885107901000957)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (109, 1), (677311, 1), (8472649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (109, 1), (677311, 1), (8472649, 1)] : List FactorBlock).map factorBlockValue).prod) = 472885107901000957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_109
      · exact prime_fortySixAR_677311
      · exact prime_fortySixAR_8472649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472885107901000957) ^ 236442553950500478 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 472885107901000957) ^ 157628369300333652 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 472885107901000957) ^ 67555015414428708 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 472885107901000957) ^ 4338395485330284 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 472885107901000957) ^ 698180168196 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 472885107901000957) ^ 55813135644 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_504093009929136949 : Nat.Prime 504093009929136949 := by
  apply lucas_primality 504093009929136949 (2 : ZMod 504093009929136949)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (971, 1), (1602309601687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (971, 1), (1602309601687, 1)] : List FactorBlock).map factorBlockValue).prod) = 504093009929136949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_971
      · exact prime_fortySixAR_1602309601687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 504093009929136949) ^ 252046504964568474 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 168031003309712316 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 519148310946588 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 314604 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_506659505133443461 : Nat.Prime 506659505133443461 := by
  apply lucas_primality 506659505133443461 (2 : ZMod 506659505133443461)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (8444325085557391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (8444325085557391, 1)] : List FactorBlock).map factorBlockValue).prod) = 506659505133443461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_8444325085557391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 506659505133443461) ^ 253329752566721730 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 506659505133443461) ^ 168886501711147820 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 506659505133443461) ^ 101331901026688692 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 506659505133443461) ^ 60 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_61717
      · exact prime_fortySixAR_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_637594244628013609 : Nat.Prime 637594244628013609 := by
  apply lucas_primality 637594244628013609 (7 : ZMod 637594244628013609)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (107556384046561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (107556384046561, 1)] : List FactorBlock).map factorBlockValue).prod) = 637594244628013609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_107556384046561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 637594244628013609) ^ 318797122314006804 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 212531414876004536 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 49045711125231816 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 33557591822527032 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 5928 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_986823496349442379 : Nat.Prime 986823496349442379 := by
  apply lucas_primality 986823496349442379 (2 : ZMod 986823496349442379)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (547, 1), (9111438852413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (547, 1), (9111438852413, 1)] : List FactorBlock).map factorBlockValue).prod) = 986823496349442379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_547
      · exact prime_fortySixAR_9111438852413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 986823496349442379) ^ 493411748174721189 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 986823496349442379) ^ 328941165449814126 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 986823496349442379) ^ 89711226940858398 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 986823496349442379) ^ 1804064892777774 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 986823496349442379) ^ 108306 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2101331033418299021 : Nat.Prime 2101331033418299021 := by
  apply lucas_primality 2101331033418299021 (2 : ZMod 2101331033418299021)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (2011, 1), (4018917173657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (2011, 1), (4018917173657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2101331033418299021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_2011
      · exact prime_fortySixAR_4018917173657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2101331033418299021) ^ 1050665516709149510 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 420266206683659804 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 161640848724484540 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 1044918465150820 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 522860 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2220757758308832079 : Nat.Prime 2220757758308832079 := by
  apply lucas_primality 2220757758308832079 (3 : ZMod 2220757758308832079)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (59, 2), (607, 1), (653, 1), (723053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (59, 2), (607, 1), (653, 1), (723053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220757758308832079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_607
      · exact prime_fortySixAR_653
      · exact prime_fortySixAR_723053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220757758308832079) ^ 1110378879154416039 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 740252586102944026 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 317251108329833154 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 41901089779411926 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 37639962005234442 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3658579502979954 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3400854147486726 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3071362345926 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2389657054025455673 : Nat.Prime 2389657054025455673 := by
  apply lucas_primality 2389657054025455673 (3 : ZMod 2389657054025455673)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (12987266597964433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (12987266597964433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2389657054025455673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_12987266597964433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2389657054025455673) ^ 1194828527012727836 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389657054025455673) ^ 103898132783715464 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389657054025455673) ^ 184 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4837721893028700913 : Nat.Prime 4837721893028700913 := by
  apply lucas_primality 4837721893028700913 (5 : ZMod 4837721893028700913)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (241, 1), (257, 1), (86467, 1), (6273037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (241, 1), (257, 1), (86467, 1), (6273037, 1)] : List FactorBlock).map factorBlockValue).prod) = 4837721893028700913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_241
      · exact prime_fortySixAR_257
      · exact prime_fortySixAR_86467
      · exact prime_fortySixAR_6273037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4837721893028700913) ^ 2418860946514350456 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 4837721893028700913) ^ 1612573964342900304 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 4837721893028700913) ^ 20073534825845232 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 4837721893028700913) ^ 18823820595442416 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 4837721893028700913) ^ 55948765344336 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 4837721893028700913) ^ 771192947376 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_439
      · exact prime_fortySixAR_853
      · exact prime_fortySixAR_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_9373918211897887979 : Nat.Prime 9373918211897887979 := by
  apply lucas_primality 9373918211897887979 (2 : ZMod 9373918211897887979)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (59, 1), (424812753190333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (59, 1), (424812753190333, 1)] : List FactorBlock).map factorBlockValue).prod) = 9373918211897887979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_424812753190333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9373918211897887979) ^ 4686959105948943989 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9373918211897887979) ^ 852174382899807998 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9373918211897887979) ^ 551406953641052234 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9373918211897887979) ^ 158879969693184542 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 9373918211897887979) ^ 22066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_14858475635311999991 : Nat.Prime 14858475635311999991 := by
  apply lucas_primality 14858475635311999991 (22 : ZMod 14858475635311999991)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (433, 1), (769, 1), (12113, 1), (28337723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (433, 1), (769, 1), (12113, 1), (28337723, 1)] : List FactorBlock).map factorBlockValue).prod) = 14858475635311999991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_433
      · exact prime_fortySixAR_769
      · exact prime_fortySixAR_12113
      · exact prime_fortySixAR_28337723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 14858475635311999991) ^ 7429237817655999995 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 2971695127062399998 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 1142959664254769230 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 34315186224739030 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 19321814870366710 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 1226655298878230 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 524335552130 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_20197150530475483867 : Nat.Prime 20197150530475483867 := by
  apply lucas_primality 20197150530475483867 (2 : ZMod 20197150530475483867)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 4), (19, 1), (277, 1), (283, 1), (941297459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 4), (19, 1), (277, 1), (283, 1), (941297459, 1)] : List FactorBlock).map factorBlockValue).prod) = 20197150530475483867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_277
      · exact prime_fortySixAR_283
      · exact prime_fortySixAR_941297459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20197150530475483867) ^ 10098575265237741933 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 6732383510158494622 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 2885307218639354838 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 1063007922656604414 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 72913900832041458 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 71368023075885102 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 21456714174 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_27530124642217745329 : Nat.Prime 27530124642217745329 := by
  apply lucas_primality 27530124642217745329 (21 : ZMod 27530124642217745329)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (52140387579957851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (52140387579957851, 1)] : List FactorBlock).map factorBlockValue).prod) = 27530124642217745329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_52140387579957851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 27530124642217745329) ^ 13765062321108872664 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (21 : ZMod 27530124642217745329) ^ 9176708214072581776 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (21 : ZMod 27530124642217745329) ^ 2502738603837976848 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (21 : ZMod 27530124642217745329) ^ 528 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_66648890454110272937 : Nat.Prime 66648890454110272937 := by
  apply lucas_primality 66648890454110272937 (3 : ZMod 66648890454110272937)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (6067, 1), (394813, 1), (151220149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (6067, 1), (394813, 1), (151220149, 1)] : List FactorBlock).map factorBlockValue).prod) = 66648890454110272937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_6067
      · exact prime_fortySixAR_394813
      · exact prime_fortySixAR_151220149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66648890454110272937) ^ 33324445227055136468 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 66648890454110272937) ^ 2897777845830881432 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 66648890454110272937) ^ 10985477246433208 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 66648890454110272937) ^ 168811286492872 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 66648890454110272937) ^ 440740806664 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_94740369555121501163 : Nat.Prime 94740369555121501163 := by
  apply lucas_primality 94740369555121501163 (2 : ZMod 94740369555121501163)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (12433, 1), (9225270165289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (12433, 1), (9225270165289, 1)] : List FactorBlock).map factorBlockValue).prod) = 94740369555121501163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_12433
      · exact prime_fortySixAR_9225270165289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94740369555121501163) ^ 47370184777560750581 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 13534338507874500166 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 1605768975510533918 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 7620073156528714 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 10269658 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_96584909776364242577 : Nat.Prime 96584909776364242577 := by
  apply lucas_primality 96584909776364242577 (3 : ZMod 96584909776364242577)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2801, 1), (535939, 1), (574463957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2801, 1), (535939, 1), (574463957, 1)] : List FactorBlock).map factorBlockValue).prod) = 96584909776364242577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_2801
      · exact prime_fortySixAR_535939
      · exact prime_fortySixAR_574463957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96584909776364242577) ^ 48292454888182121288 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 13797844253766320368 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 34482295528869776 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 180216236878384 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 168130495568 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_99001683434617988701 : Nat.Prime 99001683434617988701 := by
  apply lucas_primality 99001683434617988701 (7 : ZMod 99001683434617988701)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (112939, 1), (113623, 1), (1978189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (112939, 1), (113623, 1), (1978189, 1)] : List FactorBlock).map factorBlockValue).prod) = 99001683434617988701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_112939
      · exact prime_fortySixAR_113623
      · exact prime_fortySixAR_1978189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 99001683434617988701) ^ 49500841717308994350 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 33000561144872662900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 19800336686923597740 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 7615514110355229900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 876594298113300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 871317281136900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 99001683434617988701) ^ 50046625188300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_105058576742920434703 : Nat.Prime 105058576742920434703 := by
  apply lucas_primality 105058576742920434703 (17 : ZMod 105058576742920434703)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (6521, 1), (642113, 1), (464635181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (6521, 1), (642113, 1), (464635181, 1)] : List FactorBlock).map factorBlockValue).prod) = 105058576742920434703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_6521
      · exact prime_fortySixAR_642113
      · exact prime_fortySixAR_464635181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 105058576742920434703) ^ 52529288371460217351 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 105058576742920434703) ^ 35019525580973478234 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 105058576742920434703) ^ 16110807658782462 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 105058576742920434703) ^ 163613844826254 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 105058576742920434703) ^ 226109819142 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_131336119686186864173 : Nat.Prime 131336119686186864173 := by
  apply lucas_primality 131336119686186864173 (2 : ZMod 131336119686186864173)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4963961, 1), (6614481846563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4963961, 1), (6614481846563, 1)] : List FactorBlock).map factorBlockValue).prod) = 131336119686186864173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_4963961
      · exact prime_fortySixAR_6614481846563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131336119686186864173) ^ 65668059843093432086 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 131336119686186864173) ^ 26457927386252 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 131336119686186864173) ^ 19855844 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_195571914161591199527 : Nat.Prime 195571914161591199527 := by
  apply lucas_primality 195571914161591199527 (7 : ZMod 195571914161591199527)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (283, 1), (49361916749518223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (283, 1), (49361916749518223, 1)] : List FactorBlock).map factorBlockValue).prod) = 195571914161591199527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_283
      · exact prime_fortySixAR_49361916749518223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 195571914161591199527) ^ 97785957080795599763 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 195571914161591199527) ^ 27938844880227314218 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 195571914161591199527) ^ 691066834493255122 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 195571914161591199527) ^ 3962 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_268952083756199323169 : Nat.Prime 268952083756199323169 := by
  apply lucas_primality 268952083756199323169 (3 : ZMod 268952083756199323169)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (439, 1), (1647323, 1), (894001609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (439, 1), (1647323, 1), (894001609, 1)] : List FactorBlock).map factorBlockValue).prod) = 268952083756199323169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_439
      · exact prime_fortySixAR_1647323
      · exact prime_fortySixAR_894001609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 268952083756199323169) ^ 134476041878099661584 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 268952083756199323169) ^ 20688621827399947936 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 268952083756199323169) ^ 612647115617766112 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 268952083756199323169) ^ 163266149842016 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 268952083756199323169) ^ 300840715552 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_593236542974936803193 : Nat.Prime 593236542974936803193 := by
  apply lucas_primality 593236542974936803193 (3 : ZMod 593236542974936803193)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (1861, 1), (480079811164273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (1861, 1), (480079811164273, 1)] : List FactorBlock).map factorBlockValue).prod) = 593236542974936803193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_83
      · exact prime_fortySixAR_1861
      · exact prime_fortySixAR_480079811164273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 593236542974936803193) ^ 296618271487468401596 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 593236542974936803193) ^ 7147428228613696424 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 593236542974936803193) ^ 318772994613077272 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 593236542974936803193) ^ 1235704 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_635056563217686509789 : Nat.Prime 635056563217686509789 := by
  apply lucas_primality 635056563217686509789 (2 : ZMod 635056563217686509789)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2413558747, 1), (9397157443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2413558747, 1), (9397157443, 1)] : List FactorBlock).map factorBlockValue).prod) = 635056563217686509789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_2413558747
      · exact prime_fortySixAR_9397157443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 635056563217686509789) ^ 317528281608843254894 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 90722366173955215684 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 263120408404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 67579644916 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_766767074547667312331 : Nat.Prime 766767074547667312331 := by
  apply lucas_primality 766767074547667312331 (2 : ZMod 766767074547667312331)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (739, 1), (1250088974921609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (739, 1), (1250088974921609, 1)] : List FactorBlock).map factorBlockValue).prod) = 766767074547667312331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_83
      · exact prime_fortySixAR_739
      · exact prime_fortySixAR_1250088974921609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 766767074547667312331) ^ 383383537273833656165 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 153353414909533462466 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 9238157524670690510 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 1037573849184935470 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 613370 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_933084466357543821119 : Nat.Prime 933084466357543821119 := by
  apply lucas_primality 933084466357543821119 (7 : ZMod 933084466357543821119)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (66648890454110272937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (66648890454110272937, 1)] : List FactorBlock).map factorBlockValue).prod) = 933084466357543821119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_66648890454110272937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 933084466357543821119) ^ 466542233178771910559 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 933084466357543821119) ^ 133297780908220545874 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 933084466357543821119) ^ 14 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_107
      · exact prime_fortySixAR_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2709298883243373764647 : Nat.Prime 2709298883243373764647 := by
  apply lucas_primality 2709298883243373764647 (5 : ZMod 2709298883243373764647)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (563, 1), (3169, 1), (11003914253261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (563, 1), (3169, 1), (11003914253261, 1)] : List FactorBlock).map factorBlockValue).prod) = 2709298883243373764647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_563
      · exact prime_fortySixAR_3169
      · exact prime_fortySixAR_11003914253261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2709298883243373764647) ^ 1354649441621686882323 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 903099627747791254882 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 117795603619277120202 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 4812253789064607042 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 854938113992860134 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 246212286 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_4302043006662961223393 : Nat.Prime 4302043006662961223393 := by
  apply lucas_primality 4302043006662961223393 (3 : ZMod 4302043006662961223393)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3797, 1), (35406595722469723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3797, 1), (35406595722469723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4302043006662961223393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3797
      · exact prime_fortySixAR_35406595722469723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4302043006662961223393) ^ 2151021503331480611696 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4302043006662961223393) ^ 1133011063119031136 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 4302043006662961223393) ^ 121504 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_33221246406596460978809 : Nat.Prime 33221246406596460978809 := by
  apply lucas_primality 33221246406596460978809 (3 : ZMod 33221246406596460978809)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (593236542974936803193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (593236542974936803193, 1)] : List FactorBlock).map factorBlockValue).prod) = 33221246406596460978809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_593236542974936803193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33221246406596460978809) ^ 16610623203298230489404 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 33221246406596460978809) ^ 4745892343799494425544 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (3 : ZMod 33221246406596460978809) ^ 56 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_52818729525591298226101 : Nat.Prime 52818729525591298226101 := by
  apply lucas_primality 52818729525591298226101 (10 : ZMod 52818729525591298226101)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (11, 1), (13, 1), (149, 1), (2754375428293847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (11, 1), (13, 1), (149, 1), (2754375428293847, 1)] : List FactorBlock).map factorBlockValue).prod) = 52818729525591298226101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_149
      · exact prime_fortySixAR_2754375428293847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 52818729525591298226101) ^ 26409364762795649113050 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 17606243175197099408700 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 10563745905118259645220 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 4801702684144663475100 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 4062979194276253709700 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 354488117621418108900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 19176300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_92116162030274707997999 : Nat.Prime 92116162030274707997999 := by
  apply lucas_primality 92116162030274707997999 (13 : ZMod 92116162030274707997999)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2709298883243373764647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2709298883243373764647, 1)] : List FactorBlock).map factorBlockValue).prod) = 92116162030274707997999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_2709298883243373764647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 92116162030274707997999) ^ 46058081015137353998999 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 92116162030274707997999) ^ 5418597766486747529294 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (13 : ZMod 92116162030274707997999) ^ 34 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_120314937233924959084463 : Nat.Prime 120314937233924959084463 := by
  apply lucas_primality 120314937233924959084463 (5 : ZMod 120314937233924959084463)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1584080819, 1), (1026385466377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1584080819, 1), (1026385466377, 1)] : List FactorBlock).map factorBlockValue).prod) = 120314937233924959084463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_1584080819
      · exact prime_fortySixAR_1026385466377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 120314937233924959084463) ^ 60157468616962479542231 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 3251755060376350245526 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 75952524511898 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 117221980606 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_267196021699886626537301 : Nat.Prime 267196021699886626537301 := by
  apply lucas_primality 267196021699886626537301 (2 : ZMod 267196021699886626537301)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (127, 1), (2461807, 1), (776925863687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (127, 1), (2461807, 1), (776925863687, 1)] : List FactorBlock).map factorBlockValue).prod) = 267196021699886626537301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_127
      · exact prime_fortySixAR_2461807
      · exact prime_fortySixAR_776925863687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 267196021699886626537301) ^ 133598010849943313268650 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 267196021699886626537301) ^ 53439204339977325307460 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 267196021699886626537301) ^ 24290547427262420594300 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 267196021699886626537301) ^ 2103905682676272649900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 267196021699886626537301) ^ 108536543157073900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 267196021699886626537301) ^ 343914437900 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_430044413885039176238891 : Nat.Prime 430044413885039176238891 := by
  apply lucas_primality 430044413885039176238891 (7 : ZMod 430044413885039176238891)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (43, 1), (151, 1), (9662041, 1), (97926671179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (43, 1), (151, 1), (9662041, 1), (97926671179, 1)] : List FactorBlock).map factorBlockValue).prod) = 430044413885039176238891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_151
      · exact prime_fortySixAR_9662041
      · exact prime_fortySixAR_97926671179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 430044413885039176238891) ^ 215022206942519588119445 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 86008882777007835247778 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 61434916269291310891270 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 10001032881047422703230 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 2847976250894299180390 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 44508651317567290 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 4391494254910 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_578666943337339323546239 : Nat.Prime 578666943337339323546239 := by
  apply lucas_primality 578666943337339323546239 (17 : ZMod 578666943337339323546239)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2203, 1), (131336119686186864173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2203, 1), (131336119686186864173, 1)] : List FactorBlock).map factorBlockValue).prod) = 578666943337339323546239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_2203
      · exact prime_fortySixAR_131336119686186864173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 578666943337339323546239) ^ 289333471668669661773119 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 578666943337339323546239) ^ 262672239372373728346 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (17 : ZMod 578666943337339323546239) ^ 4406 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_796955988697682067783157 : Nat.Prime 796955988697682067783157 := by
  apply lucas_primality 796955988697682067783157 (5 : ZMod 796955988697682067783157)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (701, 1), (94740369555121501163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (701, 1), (94740369555121501163, 1)] : List FactorBlock).map factorBlockValue).prod) = 796955988697682067783157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_701
      · exact prime_fortySixAR_94740369555121501163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 796955988697682067783157) ^ 398477994348841033891578 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 265651996232560689261052 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 1136884434661458013956 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 8412 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_961039719180933119608451 : Nat.Prime 961039719180933119608451 := by
  apply lucas_primality 961039719180933119608451 (2 : ZMod 961039719180933119608451)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (191, 1), (6553, 1), (529541254218107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (191, 1), (6553, 1), (529541254218107, 1)] : List FactorBlock).map factorBlockValue).prod) = 961039719180933119608451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_191
      · exact prime_fortySixAR_6553
      · exact prime_fortySixAR_529541254218107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 961039719180933119608451) ^ 480519859590466559804225 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 961039719180933119608451) ^ 192207943836186623921690 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 961039719180933119608451) ^ 33139300661411486883050 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 961039719180933119608451) ^ 5031621566392319997950 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 961039719180933119608451) ^ 146656450355704733650 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 961039719180933119608451) ^ 1814853350 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2254270535491391681057933 : Nat.Prime 2254270535491391681057933 := by
  apply lucas_primality 2254270535491391681057933 (2 : ZMod 2254270535491391681057933)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (4302043006662961223393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (4302043006662961223393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2254270535491391681057933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_131
      · exact prime_fortySixAR_4302043006662961223393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2254270535491391681057933) ^ 1127135267745695840528966 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2254270535491391681057933) ^ 17208172026651844893572 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (2 : ZMod 2254270535491391681057933) ^ 524 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_8662675480842597054081337 : Nat.Prime 8662675480842597054081337 := by
  apply lucas_primality 8662675480842597054081337 (5 : ZMod 8662675480842597054081337)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (120314937233924959084463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (120314937233924959084463, 1)] : List FactorBlock).map factorBlockValue).prod) = 8662675480842597054081337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_120314937233924959084463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8662675480842597054081337) ^ 4331337740421298527040668 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 8662675480842597054081337) ^ 2887558493614199018027112 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (5 : ZMod 8662675480842597054081337) ^ 72 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_8837224028067894752278621 : Nat.Prime 8837224028067894752278621 := by
  apply lucas_primality 8837224028067894752278621 (6 : ZMod 8837224028067894752278621)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (1117, 1), (305351, 1), (756593, 1), (190251689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (1117, 1), (305351, 1), (756593, 1), (190251689, 1)] : List FactorBlock).map factorBlockValue).prod) = 8837224028067894752278621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_1117
      · exact prime_fortySixAR_305351
      · exact prime_fortySixAR_756593
      · exact prime_fortySixAR_190251689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8837224028067894752278621) ^ 4418612014033947376139310 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 2945741342689298250759540 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 1767444805613578950455724 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 7911570302657023054860 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 28941198909019111620 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 11680287853664909340 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 46450173843491580 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_11473476090449330022262159 : Nat.Prime 11473476090449330022262159 := by
  apply lucas_primality 11473476090449330022262159 (6 : ZMod 11473476090449330022262159)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (7283, 1), (20197150530475483867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (7283, 1), (20197150530475483867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11473476090449330022262159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_7283
      · exact prime_fortySixAR_20197150530475483867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11473476090449330022262159) ^ 5736738045224665011131079 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 3824492030149776674087386 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 882575083880717694020166 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 1575377741377087741626 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 568074 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_549336127966967922278006401 : Nat.Prime 549336127966967922278006401 := by
  apply lucas_primality 549336127966967922278006401 (71 : ZMod 549336127966967922278006401)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 549336127966967922278006401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 549336127966967922278006401) ^ 274668063983483961139003200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 183112042655655974092668800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 109867225593393584455601280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 78476589709566846039715200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 42256625228228301713692800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 32313889880409877781059200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 28912427787735153804105600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 23884179476824692272956800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 18942625102309238699241600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 17720520256998965234774400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 14846922377485619521027200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 13398442145535802982390400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 12775258789929486564604800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 11688002722701445154851200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 10364832603150338156188800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 9310781829948608852169600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 549336127966967922278006401) ^ 9005510294540457742262400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_647431865103926479827650401 : Nat.Prime 647431865103926479827650401 := by
  apply lucas_primality 647431865103926479827650401 (127 : ZMod 647431865103926479827650401)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 647431865103926479827650401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (127 : ZMod 647431865103926479827650401) ^ 323715932551963239913825200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 215810621701308826609216800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 129486373020785295965530080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 92490266443418068546807200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 58857442282175134529786400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 49802451161840498448280800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 38084227359054498813391200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 34075361321259288411981600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 28149211526257673035984800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 22325236727721602752677600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 20884898874320209026698400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 17498158516322337292639200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 15791021100095767800674400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 15056555002416894879712800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 13775146066040988932503200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 12215695567998612826936800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 10973421442439431861485600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 10613637132851253767666400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_755337175954580893132258801 : Nat.Prime 755337175954580893132258801 := by
  apply lucas_primality 755337175954580893132258801 (71 : ZMod 755337175954580893132258801)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 755337175954580893132258801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 755337175954580893132258801) ^ 377668587977290446566129400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 251779058651526964377419600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 151067435190916178626451760 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 107905310850654413304608400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 68667015995870990284750800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 58102859688813914856327600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 44431598585563581948956400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 39754588208135836480645200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 32840746780633951875315600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 26046109515675203211457200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 24365715353373577197814800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 20414518269042726841412400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 18422857950111729100786800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 17565980836153044026331600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 16071003743714487087920400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 14251644829331714964759600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 12802325016179337171733200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 12382576654993129395610800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_836681179518920373931117441 : Nat.Prime 836681179518920373931117441 := by
  apply lucas_primality 836681179518920373931117441 (71 : ZMod 836681179518920373931117441)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 836681179518920373931117441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 836681179518920373931117441) ^ 418340589759460186965558720 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 278893726506306791310372480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 167336235903784074786223488 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 119525882788417196275873920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 76061925410810943084647040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 49216539971701198466536320 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 44035851553627388101637760 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 36377442587779146692657280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 28851075155824840480383360 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 26989715468352270126810240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 22613004851862712808949120 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 20406858037046838388563840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 19457701849277217998398080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 17801727223806816466619520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 15786437349413591960964480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 14181036940998650405612160 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 836681179518920373931117441) ^ 13716084910146235638215040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_891545519159505316483977601 : Nat.Prime 891545519159505316483977601 := by
  apply lucas_primality 891545519159505316483977601 (139 : ZMod 891545519159505316483977601)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 891545519159505316483977601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (139 : ZMod 891545519159505316483977601) ^ 445772759579752658241988800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 297181839719835105494659200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 178309103831901063296795520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 127363645594215045211996800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 81049592650864119680361600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 68580424550731178191075200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 52443854068206195087292800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 46923448376816069288630400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 38762848659108926803651200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 30742948936534666085654400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 28759532876113074725289600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 24095824842148792337404800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 21745012662426958938633600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 20733616724639658522883200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 18969053599138410989020800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 16821613569047270122339200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (139 : ZMod 891545519159505316483977601) ^ 15110941002703479940406400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_921767401164912276364790401 : Nat.Prime 921767401164912276364790401 := by
  apply lucas_primality 921767401164912276364790401 (142 : ZMod 921767401164912276364790401)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 921767401164912276364790401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (142 : ZMod 921767401164912276364790401) ^ 460883700582456138182395200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 307255800388304092121596800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 184353480232982455272958080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 131681057309273182337827200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 83797036469537479669526400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 70905184704993252028060800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 54221611833230133903811200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 48514073745521698756041600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 40076843528909229407164800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 31785082798790078495337600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 29734432295642331495638400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 24912632463916548009859200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 22482131735729567716214400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 21436451189881680845692800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 19612072365210899497123200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 17391837757828533516316800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (142 : ZMod 921767401164912276364790401) ^ 15110941002703479940406400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1157112269547443070330268801 : Nat.Prime 1157112269547443070330268801 := by
  apply lucas_primality 1157112269547443070330268801 (89 : ZMod 1157112269547443070330268801)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157112269547443070330268801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 1157112269547443070330268801) ^ 578556134773721535165134400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 385704089849147690110089600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 231422453909488614066053760 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 165301752792491867190038400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 105192024504313006393660800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 89008636119034082333097600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 68065427620437827666486400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 60900645765654898438435200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 50309229110758394362185600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 39900423087842864494147200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 37326202243465905494524800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 31273304582363326225142400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 28222250476766904154396800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 26909587663894024891401600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 21832306972593265477929600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 19612072365210899497123200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 1157112269547443070330268801) ^ 18969053599138410989020800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1326445772408044495256649601 : Nat.Prime 1326445772408044495256649601 := by
  apply lucas_primality 1326445772408044495256649601 (67 : ZMod 1326445772408044495256649601)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1326445772408044495256649601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1326445772408044495256649601) ^ 663222886204022247628324800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 442148590802681498418883200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 265289154481608899051329920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 189492253201149213608092800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 120585979309822226841513600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 102034290185234191942819200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 78026221906355558544508800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 69812935389897078697718400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 57671555322088891098115200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 45739509393380844664022400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 42788573303485306298601600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 35849885740757959331260800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 30847576102512662680387200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 28222250476766904154396800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 25027278724680084816163200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 22482131735729567716214400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 1326445772408044495256649601) ^ 21745012662426958938633600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1553836476249423551586360961 : Nat.Prime 1553836476249423551586360961 := by
  apply lucas_primality 1553836476249423551586360961 (73 : ZMod 1553836476249423551586360961)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553836476249423551586360961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 1553836476249423551586360961) ^ 776918238124711775793180480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 517945492083141183862120320 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 310767295249884710317272192 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 221976639464203364512337280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 141257861477220322871487360 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 119525882788417196275873920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 91402145661730797152138880 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 81780867171022292188755840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 67558107663018415286363520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 53580568146531846606426240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 50123757298368501664076160 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 41995580439173609502334080 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 37898450640229842721618560 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 36135732005800547711310720 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 33060350558498373438007680 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 29317669363196670784648320 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 26336211461854636467565440 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 1553836476249423551586360961) ^ 25472729118843009042399360 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_1648008383900903766834019201 : Nat.Prime 1648008383900903766834019201 := by
  apply lucas_primality 1648008383900903766834019201 (11 : ZMod 1648008383900903766834019201)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1648008383900903766834019201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1648008383900903766834019201) ^ 824004191950451883417009600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 549336127966967922278006400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 329601676780180753366803840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 235429769128700538119145600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 126769875684684905141078400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 96941669641229633343177600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 86737283363205461412316800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 71652538430474076818870400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 56827875306927716097724800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 53161560770996895704323200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 44540767132456858563081600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 40195326436607408947171200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 38325776369788459693814400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 35064008168104335464553600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 31094497809451014468566400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 27932345489845826556508800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (11 : ZMod 1648008383900903766834019201) ^ 27016530883621373226787200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2589727460415705919310601601 : Nat.Prime 2589727460415705919310601601 := by
  apply lucas_primality 2589727460415705919310601601 (71 : ZMod 2589727460415705919310601601)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2589727460415705919310601601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 2589727460415705919310601601) ^ 1294863730207852959655300800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 863242486805235306436867200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 517945492083141183862120320 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 369961065773672274187228800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 235429769128700538119145600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 199209804647361993793123200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 152336909436217995253564800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 136301445285037153647926400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 112596846105030692143939200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 89300946910886411010710400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 83539595497280836106793600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 69992634065289349170556800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 63164084400383071202697600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 60226220009667579518851200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 55100584264163955730012800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 48862782271994451307747200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 43893685769757727445942400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (71 : ZMod 2589727460415705919310601601) ^ 42454548531405015070665600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_2719213833436491215276131681 : Nat.Prime 2719213833436491215276131681 := by
  apply lucas_primality 2719213833436491215276131681 (67 : ZMod 2719213833436491215276131681)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719213833436491215276131681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 2719213833436491215276131681) ^ 1359606916718245607638065840 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 906404611145497071758710560 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 543842766687298243055226336 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 388459119062355887896590240 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 247201257585135565025102880 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 209170294879730093482779360 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 159953754908028895016243040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 143116517549289011330322720 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 118226688410282226751136160 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 93765994256430731561245920 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 87716575272144877912133280 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 73492265768553816629084640 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 66322288620402224762832480 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 63237531010150958494793760 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 57855613477372153516513440 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 51305921385594173873134560 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 46088370058245613818239520 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 44577275957975265824198880 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_3021348703818323572529035201 : Nat.Prime 3021348703818323572529035201 := by
  apply lucas_primality 3021348703818323572529035201 (73 : ZMod 3021348703818323572529035201)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3021348703818323572529035201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 3021348703818323572529035201) ^ 1510674351909161786264517600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 1007116234606107857509678400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 604269740763664714505807040 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 431621243402617653218433600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 274668063983483961139003200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 232411438755255659425310400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 177726394342254327795825600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 159018352832543345922580800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 131362987122535807501262400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 104184438062700812845828800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 97462861413494308791259200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 81658073076170907365649600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 73691431800446916403147200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 70263923344612176105326400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 64284014974857948351681600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 57006579317326859859038400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 51209300064717348686932800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 49530306619972517582443200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem prime_fortySixAR_7769182381247117757931804801 : Nat.Prime 7769182381247117757931804801 := by
  apply lucas_primality 7769182381247117757931804801 (89 : ZMod 7769182381247117757931804801)
  · rw [← fortySixARFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7769182381247117757931804801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySixAR_2
      · exact prime_fortySixAR_3
      · exact prime_fortySixAR_5
      · exact prime_fortySixAR_7
      · exact prime_fortySixAR_11
      · exact prime_fortySixAR_13
      · exact prime_fortySixAR_17
      · exact prime_fortySixAR_19
      · exact prime_fortySixAR_23
      · exact prime_fortySixAR_29
      · exact prime_fortySixAR_31
      · exact prime_fortySixAR_37
      · exact prime_fortySixAR_41
      · exact prime_fortySixAR_43
      · exact prime_fortySixAR_47
      · exact prime_fortySixAR_53
      · exact prime_fortySixAR_59
      · exact prime_fortySixAR_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 7769182381247117757931804801) ^ 3884591190623558878965902400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 2589727460415705919310601600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 1553836476249423551586360960 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 1109883197321016822561686400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 706289307386101614357436800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 597629413942085981379369600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 457010728308653985760694400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 408904335855111460943779200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 337790538315092076431817600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 267902840732659233032131200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 250618786491842508320380800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 209977902195868047511670400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 189492253201149213608092800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 180678660029002738556553600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 165301752792491867190038400 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 146588346815983353923241600 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 131681057309273182337827200 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide
    · change (89 : ZMod 7769182381247117757931804801) ^ 127363645594215045211996800 ≠ 1
      rw [← fortySixARFastPow_eq_pow]
      decide

private theorem phi_fortySixAR_54384276668729824305522633600 : Nat.totient 54384276668729824305522633600 = 7156282949130589411737600000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_7, prime_fortySixAR_11, prime_fortySixAR_13, prime_fortySixAR_17, prime_fortySixAR_19, prime_fortySixAR_23, prime_fortySixAR_29, prime_fortySixAR_31, prime_fortySixAR_37, prime_fortySixAR_41, prime_fortySixAR_43, prime_fortySixAR_47, prime_fortySixAR_53, prime_fortySixAR_59, prime_fortySixAR_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633601 : Nat.totient 54384276668729824305522633601 = 54384222365100378497800548000 := by
  rw [← show ((([(1068233, 1), (16027751, 1), (3176397018450847, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_1068233, prime_fortySixAR_16027751, prime_fortySixAR_3176397018450847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633602 : Nat.totient 54384276668729824305522633602 = 27123638399188497816369342480 := by
  rw [← show ((([(2, 1), (397, 1), (4609763, 1), (14858475635311999991, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_397, prime_fortySixAR_4609763, prime_fortySixAR_14858475635311999991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633603 : Nat.totient 54384276668729824305522633603 = 36224198628575828456030054400 := by
  rw [← show ((([(3, 1), (1423, 1), (6361, 1), (44647, 1), (44856927592740961, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_1423, prime_fortySixAR_6361, prime_fortySixAR_44647, prime_fortySixAR_44856927592740961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633604 : Nat.totient 54384276668729824305522633604 = 26732372565077651030331801600 := by
  rw [← show ((([(2, 2), (107, 1), (131, 1), (133660878913, 1), (7256947469281, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_107, prime_fortySixAR_131, prime_fortySixAR_133660878913, prime_fortySixAR_7256947469281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633605 : Nat.totient 54384276668729824305522633605 = 43507421315632971863309933568 := by
  rw [← show ((([(5, 1), (2248342417, 1), (4837721893028700913, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_2248342417, prime_fortySixAR_4837721893028700913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633606 : Nat.totient 54384276668729824305522633606 = 17825904664842595427241696000 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (571, 1), (52051, 1), (7369849, 1), (617623095907, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_67, prime_fortySixAR_571, prime_fortySixAR_52051, prime_fortySixAR_7369849, prime_fortySixAR_617623095907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633607 : Nat.totient 54384276668729824305522633607 = 46615094287482706547590828800 := by
  rw [← show ((([(7, 1), (7769182381247117757931804801, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_7, prime_fortySixAR_7769182381247117757931804801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633608 : Nat.totient 54384276668729824305522633608 = 27192138324806283925280397568 := by
  rw [← show ((([(2, 3), (2844774137, 1), (2389657054025455673, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_2844774137, prime_fortySixAR_2389657054025455673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633609 : Nat.totient 54384276668729824305522633609 = 36256154790020813815485290688 := by
  rw [← show ((([(3, 2), (1225507, 1), (509541427, 1), (9676884376009, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_1225507, prime_fortySixAR_509541427, prime_fortySixAR_9676884376009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633610 : Nat.totient 54384276668729824305522633610 = 21671414279039831300776800000 := by
  rw [← show ((([(2, 1), (5, 1), (277, 1), (6451, 1), (53819, 1), (46324247, 1), (1220738251, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_277, prime_fortySixAR_6451, prime_fortySixAR_53819, prime_fortySixAR_46324247, prime_fortySixAR_1220738251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633611 : Nat.totient 54384276668729824305522633611 = 49427949883689773680121167680 := by
  rw [← show ((([(11, 1), (4019, 1), (15443297417, 1), (79656758553187, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_11, prime_fortySixAR_4019, prime_fortySixAR_15443297417, prime_fortySixAR_79656758553187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633612 : Nat.totient 54384276668729824305522633612 = 18127723758261820336342022416 := by
  rw [← show ((([(2, 2), (3, 1), (49199, 1), (92116162030274707997999, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_49199, prime_fortySixAR_92116162030274707997999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633613 : Nat.totient 54384276668729824305522633613 = 49513187609748542298450843648 := by
  rw [← show ((([(13, 2), (73, 1), (369210834673, 1), (11939588383213, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_13, prime_fortySixAR_73, prime_fortySixAR_369210834673, prime_fortySixAR_11939588383213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633614 : Nat.totient 54384276668729824305522633614 = 23242615705469605199457212928 := by
  rw [← show ((([(2, 1), (7, 1), (359, 1), (2970797, 1), (279560689, 1), (13028721283, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_7, prime_fortySixAR_359, prime_fortySixAR_2970797, prime_fortySixAR_279560689, prime_fortySixAR_13028721283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633615 : Nat.totient 54384276668729824305522633615 = 29004946716187292352639176736 := by
  rw [← show ((([(3, 1), (5, 1), (34510447, 1), (105058576742920434703, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_34510447, prime_fortySixAR_105058576742920434703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633616 : Nat.totient 54384276668729824305522633616 = 26809150313138072054435232000 := by
  rw [← show ((([(2, 4), (71, 1), (170365511, 1), (281004545474211721, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_71, prime_fortySixAR_170365511, prime_fortySixAR_281004545474211721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633617 : Nat.totient 54384276668729824305522633617 = 51171266030266487886069173760 := by
  rw [← show ((([(17, 1), (3673, 1), (4951267327, 1), (175908624084631, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_17, prime_fortySixAR_3673, prime_fortySixAR_4951267327, prime_fortySixAR_175908624084631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633618 : Nat.totient 54384276668729824305522633618 = 18128092222909941435174211200 := by
  rw [← show ((([(2, 1), (3, 2), (3021348703818323572529035201, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_3021348703818323572529035201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633619 : Nat.totient 54384276668729824305522633619 = 51521941476606536467136796672 := by
  rw [← show ((([(19, 1), (10642529, 1), (268952083756199323169, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_19, prime_fortySixAR_10642529, prime_fortySixAR_268952083756199323169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633620 : Nat.totient 54384276668729824305522633620 = 21753710667491929722209053440 := by
  rw [← show ((([(2, 2), (5, 1), (2719213833436491215276131681, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_2719213833436491215276131681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633621 : Nat.totient 54384276668729824305522633621 = 31076729524988471031727219200 := by
  rw [← show ((([(3, 1), (7, 1), (2589727460415705919310601601, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_7, prime_fortySixAR_2589727460415705919310601601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633622 : Nat.totient 54384276668729824305522633622 = 24704685305701779257285952000 := by
  rw [← show ((([(2, 1), (11, 1), (1601, 1), (1009161947, 1), (1530024826764883, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_11, prime_fortySixAR_1601, prime_fortySixAR_1009161947, prime_fortySixAR_1530024826764883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633623 : Nat.totient 54384276668729824305522633623 = 52019495414913809662167366144 := by
  rw [← show ((([(23, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_23, prime_fortySixAR_210193, prime_fortySixAR_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633624 : Nat.totient 54384276668729824305522633624 = 17951481427491061253822720000 := by
  rw [← show ((([(2, 3), (3, 1), (173, 1), (251, 1), (989777, 1), (52723584966097631, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_173, prime_fortySixAR_251, prime_fortySixAR_989777, prime_fortySixAR_52723584966097631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633625 : Nat.totient 54384276668729824305522633625 = 43281994281434720276312294400 := by
  rw [← show ((([(5, 3), (193, 1), (2254270535491391681057933, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_193, prime_fortySixAR_2254270535491391681057933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633626 : Nat.totient 54384276668729824305522633626 = 25100251211812731893060131584 := by
  rw [← show ((([(2, 1), (13, 1), (136303, 1), (1140538079, 1), (13455034150673, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_13, prime_fortySixAR_136303, prime_fortySixAR_1140538079, prime_fortySixAR_13455034150673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633627 : Nat.totient 54384276668729824305522633627 = 36256184445815376591366876672 := by
  rw [← show ((([(3, 3), (8322364437809, 1), (242026467870289, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_8322364437809, prime_fortySixAR_242026467870289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633628 : Nat.totient 54384276668729824305522633628 = 23201757246478613395116625920 := by
  rw [← show ((([(2, 2), (7, 1), (337, 1), (677, 1), (13613, 1), (38803, 1), (16116755127691, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_7, prime_fortySixAR_337, prime_fortySixAR_677, prime_fortySixAR_13613, prime_fortySixAR_38803, prime_fortySixAR_16116755127691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633629 : Nat.totient 54384276668729824305522633629 = 52208606262879105448344755904 := by
  rw [← show ((([(29, 1), (179, 1), (7907, 1), (130303, 1), (10168483172098039, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_29, prime_fortySixAR_179, prime_fortySixAR_7907, prime_fortySixAR_130303, prime_fortySixAR_10168483172098039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633630 : Nat.totient 54384276668729824305522633630 = 14502473005648674937075275776 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (18769073, 1), (96584909776364242577, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_18769073, prime_fortySixAR_96584909776364242577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633631 : Nat.totient 54384276668729824305522633631 = 52629939296129501899274874360 := by
  rw [← show ((([(31, 1), (8970263, 1), (195571914161591199527, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_31, prime_fortySixAR_8970263, prime_fortySixAR_195571914161591199527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633632 : Nat.totient 54384276668729824305522633632 = 27188253855958326597328574208 := by
  rw [← show ((([(2, 5), (7517, 1), (101807, 1), (2220757758308832079, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_7517, prime_fortySixAR_101807, prime_fortySixAR_2220757758308832079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633633 : Nat.totient 54384276668729824305522633633 = 32960167678018075336680384000 := by
  rw [← show ((([(3, 1), (11, 1), (1648008383900903766834019201, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_11, prime_fortySixAR_1648008383900903766834019201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633634 : Nat.totient 54384276668729824305522633634 = 25451205200835536886562425600 := by
  rw [← show ((([(2, 1), (17, 1), (181, 1), (8837224028067894752278621, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_17, prime_fortySixAR_181, prime_fortySixAR_8837224028067894752278621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633635 : Nat.totient 54384276668729824305522633635 = 37292075429986165238072663040 := by
  rw [← show ((([(5, 1), (7, 1), (1553836476249423551586360961, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_7, prime_fortySixAR_1553836476249423551586360961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633636 : Nat.totient 54384276668729824305522633636 = 18128092222908618030015228144 := by
  rw [← show ((([(2, 2), (3, 2), (16027271091163, 1), (94256492157427, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_16027271091163, prime_fortySixAR_94256492157427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633637 : Nat.totient 54384276668729824305522633637 = 52904812296577552054385400000 := by
  rw [← show ((([(37, 1), (5501, 1), (267196021699886626537301, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_37, prime_fortySixAR_5501, prime_fortySixAR_267196021699886626537301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633638 : Nat.totient 54384276668729824305522633638 = 25494695107795660378105184256 := by
  rw [← show ((([(2, 1), (19, 1), (97, 1), (56437, 1), (104009, 1), (6260129, 1), (401513269, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_19, prime_fortySixAR_97, prime_fortySixAR_56437, prime_fortySixAR_104009, prime_fortySixAR_6260129, prime_fortySixAR_401513269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633639 : Nat.totient 54384276668729824305522633639 = 33444182227496472562374060000 := by
  rw [← show ((([(3, 1), (13, 1), (1451, 1), (961039719180933119608451, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_13, prime_fortySixAR_1451, prime_fortySixAR_961039719180933119608451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633640 : Nat.totient 54384276668729824305522633640 = 21752865567819520261437024000 := by
  rw [← show ((([(2, 3), (5, 1), (25741, 1), (52818729525591298226101, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_25741, prime_fortySixAR_52818729525591298226101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633641 : Nat.totient 54384276668729824305522633641 = 53057830896321779810265984000 := by
  rw [← show ((([(41, 1), (1326445772408044495256649601, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_41, prime_fortySixAR_1326445772408044495256649601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633642 : Nat.totient 54384276668729824305522633642 = 15533204229527615045748706800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3011, 1), (430044413885039176238891, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_7, prime_fortySixAR_3011, prime_fortySixAR_430044413885039176238891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633643 : Nat.totient 54384276668729824305522633643 = 52750349170664806889087827968 := by
  rw [← show ((([(43, 1), (367, 1), (617, 1), (619, 1), (1097, 1), (20593, 1), (21649, 1), (18450109, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_43, prime_fortySixAR_367, prime_fortySixAR_617, prime_fortySixAR_619, prime_fortySixAR_1097, prime_fortySixAR_20593, prime_fortySixAR_21649, prime_fortySixAR_18450109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633644 : Nat.totient 54384276668729824305522633644 = 24720110423172065549131802000 := by
  rw [← show ((([(2, 2), (11, 1), (1611971, 1), (766767074547667312331, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_11, prime_fortySixAR_1611971, prime_fortySixAR_766767074547667312331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633645 : Nat.totient 54384276668729824305522633645 = 28555605926658840328626862080 := by
  rw [← show ((([(3, 2), (5, 1), (109, 1), (157, 1), (149341, 1), (472885107901000957, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_109, prime_fortySixAR_157, prime_fortySixAR_149341, prime_fortySixAR_472885107901000957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633646 : Nat.totient 54384276668729824305522633646 = 25752206212772504069021476224 := by
  rw [← show ((([(2, 1), (23, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_23, prime_fortySixAR_103, prime_fortySixAR_5009, prime_fortySixAR_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633647 : Nat.totient 54384276668729824305522633647 = 53227164399182381235192364800 := by
  rw [← show ((([(47, 1), (1157112269547443070330268801, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_47, prime_fortySixAR_1157112269547443070330268801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633648 : Nat.totient 54384276668729824305522633648 = 18115683147240447330243182592 := by
  rw [← show ((([(2, 4), (3, 1), (1499, 1), (63667, 1), (1216489, 1), (1318897, 1), (7399409, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_1499, prime_fortySixAR_63667, prime_fortySixAR_1216489, prime_fortySixAR_1318897, prime_fortySixAR_7399409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633649 : Nat.totient 54384276668729824305522633649 = 46326789776898051133798998528 := by
  rw [← show ((([(7, 2), (167, 1), (9173, 1), (11243, 1), (64441731532011377, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_7, prime_fortySixAR_167, prime_fortySixAR_9173, prime_fortySixAR_11243, prime_fortySixAR_64441731532011377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633650 : Nat.totient 54384276668729824305522633650 = 21736806173780630858462472000 := by
  rw [← show ((([(2, 1), (5, 2), (1291, 1), (400943, 1), (2101331033418299021, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_1291, prime_fortySixAR_400943, prime_fortySixAR_2101331033418299021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633651 : Nat.totient 54384276668729824305522633651 = 34123467413747448152425843328 := by
  rw [← show ((([(3, 1), (17, 1), (113758019, 1), (9373918211897887979, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_17, prime_fortySixAR_113758019, prime_fortySixAR_9373918211897887979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633652 : Nat.totient 54384276668729824305522633652 = 25100215011259044008006603520 := by
  rw [← show ((([(2, 2), (13, 1), (113903, 1), (3330424087, 1), (2756990764841, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_13, prime_fortySixAR_113903, prime_fortySixAR_3330424087, prime_fortySixAR_2756990764841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633653 : Nat.totient 54384276668729824305522633653 = 53338476019305598438322216640 := by
  rw [← show ((([(53, 1), (2711, 1), (419349797, 1), (902592108976603, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_53, prime_fortySixAR_2711, prime_fortySixAR_419349797, prime_fortySixAR_902592108976603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633654 : Nat.totient 54384276668729824305522633654 = 18128007783865758228817651200 := by
  rw [← show ((([(2, 1), (3, 4), (214691, 1), (27262846097, 1), (57355267721, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_214691, prime_fortySixAR_27262846097, prime_fortySixAR_57355267721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633655 : Nat.totient 54384276668729824305522633655 = 39521820105986050781031484800 := by
  rw [← show ((([(5, 1), (11, 1), (1303, 1), (1497787, 1), (506659505133443461, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_11, prime_fortySixAR_1303, prime_fortySixAR_1497787, prime_fortySixAR_506659505133443461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633656 : Nat.totient 54384276668729824305522633656 = 23076763231557312882993024000 := by
  rw [← show ((([(2, 3), (7, 1), (101, 1), (1469231, 1), (56041753, 1), (116778303307, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_7, prime_fortySixAR_101, prime_fortySixAR_1469231, prime_fortySixAR_56041753, prime_fortySixAR_116778303307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633657 : Nat.totient 54384276668729824305522633657 = 33934133315802314797036232832 := by
  rw [← show ((([(3, 1), (19, 1), (83, 1), (17779879363, 1), (646534342540169, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_19, prime_fortySixAR_83, prime_fortySixAR_17779879363, prime_fortySixAR_646534342540169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633658 : Nat.totient 54384276668729824305522633658 = 26254453968680248522637569920 := by
  rw [← show ((([(2, 1), (29, 1), (1076003, 1), (1137479177, 1), (766105227571, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_29, prime_fortySixAR_1076003, prime_fortySixAR_1137479177, prime_fortySixAR_766105227571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633659 : Nat.totient 54384276668729824305522633659 = 53462509267564912029157843200 := by
  rw [← show ((([(59, 1), (921767401164912276364790401, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_59, prime_fortySixAR_921767401164912276364790401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633660 : Nat.totient 54384276668729824305522633660 = 14318898160880763867783173184 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (79, 1), (11473476090449330022262159, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_79, prime_fortySixAR_11473476090449330022262159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633661 : Nat.totient 54384276668729824305522633661 = 53492731149570318989038656000 := by
  rw [← show ((([(61, 1), (891545519159505316483977601, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_61, prime_fortySixAR_891545519159505316483977601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633662 : Nat.totient 54384276668729824305522633662 = 26306508306212477235408852000 := by
  rw [← show ((([(2, 1), (31, 1), (3109, 1), (177900851, 1), (1585926001599839, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_31, prime_fortySixAR_3109, prime_fortySixAR_177900851, prime_fortySixAR_1585926001599839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633663 : Nat.totient 54384276668729824305522633663 = 30937371992957314950870453120 := by
  rw [← show ((([(3, 2), (7, 1), (223, 1), (58538318617, 1), (66128352046711, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_7, prime_fortySixAR_223, prime_fortySixAR_58538318617, prime_fortySixAR_66128352046711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633664 : Nat.totient 54384276668729824305522633664 = 27191133900739895142327290880 := by
  rw [← show ((([(2, 6), (27077, 1), (149921671, 1), (209328529952453, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_27077, prime_fortySixAR_149921671, prime_fortySixAR_209328529952453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633665 : Nat.totient 54384276668729824305522633665 = 40160696616908177948693637120 := by
  rw [← show ((([(5, 1), (13, 1), (836681179518920373931117441, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_13, prime_fortySixAR_836681179518920373931117441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633666 : Nat.totient 54384276668729824305522633666 = 16479929498054791734734772960 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (116927, 1), (1230067, 1), (520826605545199, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_11, prime_fortySixAR_116927, prime_fortySixAR_1230067, prime_fortySixAR_520826605545199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633667 : Nat.totient 54384276668729824305522633667 = 54275290142087694128281119144 := by
  rw [← show ((([(499, 1), (215564018827, 1), (505587745966579, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_499, prime_fortySixAR_215564018827, prime_fortySixAR_505587745966579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633668 : Nat.totient 54384276668729824305522633668 = 25591612559064647061274337280 := by
  rw [← show ((([(2, 2), (17, 1), (39679, 1), (74561, 1), (270328603841520479, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_17, prime_fortySixAR_39679, prime_fortySixAR_74561, prime_fortySixAR_270328603841520479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633669 : Nat.totient 54384276668729824305522633669 = 34574094043739776067173632000 := by
  rw [← show ((([(3, 1), (23, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_23, prime_fortySixAR_421, prime_fortySixAR_1483, prime_fortySixAR_2072201, prime_fortySixAR_2567179, prime_fortySixAR_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633670 : Nat.totient 54384276668729824305522633670 = 18646037714977573807770078336 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1204531986989, 1), (644995937440229, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_7, prime_fortySixAR_1204531986989, prime_fortySixAR_644995937440229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633671 : Nat.totient 54384276668729824305522633671 = 53618108883305582425874684928 := by
  rw [← show ((([(89, 1), (457, 1), (1433, 1), (933084466357543821119, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_89, prime_fortySixAR_457, prime_fortySixAR_1433, prime_fortySixAR_933084466357543821119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633672 : Nat.totient 54384276668729824305522633672 = 18128092222909941435174211200 := by
  rw [← show ((([(2, 3), (3, 2), (755337175954580893132258801, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_755337175954580893132258801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633673 : Nat.totient 54384276668729824305522633673 = 53572571043217671248817033504 := by
  rw [← show ((([(67, 1), (14919349673, 1), (54406233496243403, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_67, prime_fortySixAR_14919349673, prime_fortySixAR_54406233496243403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633674 : Nat.totient 54384276668729824305522633674 = 26455023444407000035772066688 := by
  rw [← show ((([(2, 1), (37, 1), (13177, 1), (143467, 1), (388752391739653339, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_37, prime_fortySixAR_13177, prime_fortySixAR_143467, prime_fortySixAR_388752391739653339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633675 : Nat.totient 54384276668729824305522633675 = 28955383421455043155246448640 := by
  rw [← show ((([(3, 1), (5, 2), (593, 1), (44417, 1), (27530124642217745329, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_593, prime_fortySixAR_44417, prime_fortySixAR_27530124642217745329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633676 : Nat.totient 54384276668729824305522633676 = 25758026007607103405351040000 := by
  rw [← show ((([(2, 2), (19, 1), (8741, 1), (2960967601, 1), (27648080720861, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_19, prime_fortySixAR_8741, prime_fortySixAR_2960967601, prime_fortySixAR_27648080720861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633677 : Nat.totient 54384276668729824305522633677 = 42205967311136110345892736000 := by
  rw [← show ((([(7, 1), (11, 1), (263, 1), (5651, 1), (15377, 1), (938207, 1), (32940583843, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_7, prime_fortySixAR_11, prime_fortySixAR_263, prime_fortySixAR_5651, prime_fortySixAR_15377, prime_fortySixAR_938207, prime_fortySixAR_32940583843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633678 : Nat.totient 54384276668729824305522633678 = 16733608349020890254119764096 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1097909, 1), (635056563217686509789, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_13, prime_fortySixAR_1097909, prime_fortySixAR_635056563217686509789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633679 : Nat.totient 54384276668729824305522633679 = 54384276668718745968535477384 := by
  rw [← show ((([(4911242276933, 1), (11073425744879363, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_4911242276933, prime_fortySixAR_11073425744879363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633680 : Nat.totient 54384276668729824305522633680 = 21728208075853603896039965184 := by
  rw [← show ((([(2, 4), (5, 1), (853, 1), (796955988697682067783157, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_853, prime_fortySixAR_796955988697682067783157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633681 : Nat.totient 54384276668729824305522633681 = 35957230713303902428691865600 := by
  rw [← show ((([(3, 3), (127, 1), (4817, 1), (6007, 1), (2039771, 1), (268713929761, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_127, prime_fortySixAR_4817, prime_fortySixAR_6007, prime_fortySixAR_2039771, prime_fortySixAR_268713929761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633682 : Nat.totient 54384276668729824305522633682 = 26295268562571937084682803200 := by
  rw [← show ((([(2, 1), (41, 1), (139, 1), (661, 1), (9349, 1), (198223, 1), (3895148684197, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_41, prime_fortySixAR_139, prime_fortySixAR_661, prime_fortySixAR_9349, prime_fortySixAR_198223, prime_fortySixAR_3895148684197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633683 : Nat.totient 54384276668729824305522633683 = 54384276667743000754062751728 := by
  rw [← show ((([(55110439577, 1), (986823496349442379, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_55110439577, prime_fortySixAR_986823496349442379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633684 : Nat.totient 54384276668729824305522633684 = 15538364762494235515863609600 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (647431865103926479827650401, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_7, prime_fortySixAR_647431865103926479827650401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633685 : Nat.totient 54384276668729824305522633685 = 40886382707405662350190924800 := by
  rw [← show ((([(5, 1), (17, 1), (1171, 1), (1559, 1), (72139, 1), (4858266148135991, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_17, prime_fortySixAR_1171, prime_fortySixAR_1559, prime_fortySixAR_72139, prime_fortySixAR_4858266148135991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633686 : Nat.totient 54384276668729824305522633686 = 26195930654068013491541960064 := by
  rw [← show ((([(2, 1), (43, 1), (73, 1), (8662675480842597054081337, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_43, prime_fortySixAR_73, prime_fortySixAR_8662675480842597054081337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633687 : Nat.totient 54384276668729824305522633687 = 34164039488775859862454528000 := by
  rw [← show ((([(3, 1), (29, 1), (71, 1), (113, 1), (787, 1), (99001683434617988701, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_29, prime_fortySixAR_71, prime_fortySixAR_113, prime_fortySixAR_787, prime_fortySixAR_99001683434617988701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633688 : Nat.totient 54384276668729824305522633688 = 24649293019471977864327626880 := by
  rw [← show ((([(2, 3), (11, 1), (349, 1), (17199463, 1), (102955693875907123, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_11, prime_fortySixAR_349, prime_fortySixAR_17199463, prime_fortySixAR_102955693875907123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633689 : Nat.totient 54384276668729824305522633689 = 54384008287624592861023458336 := by
  rw [← show ((([(202639, 1), (55142972383, 1), (4866986602697, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_202639, prime_fortySixAR_55142972383, prime_fortySixAR_4866986602697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633690 : Nat.totient 54384276668729824305522633690 = 14502264292373188410838245888 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (69233, 1), (1157796803, 1), (7538507136859, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_5, prime_fortySixAR_69233, prime_fortySixAR_1157796803, prime_fortySixAR_7538507136859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633691 : Nat.totient 54384276668729824305522633691 = 43026423672500730025166891520 := by
  rw [← show ((([(7, 1), (13, 1), (14929, 1), (3625591, 1), (11041356593572759, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_7, prime_fortySixAR_13, prime_fortySixAR_14929, prime_fortySixAR_3625591, prime_fortySixAR_11041356593572759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633692 : Nat.totient 54384276668729824305522633692 = 26009871428988138796817068400 := by
  rw [← show ((([(2, 2), (23, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_23, prime_fortySixAR_1222615931, prime_fortySixAR_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633693 : Nat.totient 54384276668729824305522633693 = 35086383067496533822013400000 := by
  rw [← show ((([(3, 1), (31, 1), (192461, 1), (541991, 1), (5606032292852851, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_31, prime_fortySixAR_192461, prime_fortySixAR_541991, prime_fortySixAR_5606032292852851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633694 : Nat.totient 54384276668729824305522633694 = 26576265401163536020157310336 := by
  rw [← show ((([(2, 1), (47, 2), (733, 1), (26339, 1), (637594244628013609, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_47, prime_fortySixAR_733, prime_fortySixAR_26339, prime_fortySixAR_637594244628013609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633695 : Nat.totient 54384276668729824305522633695 = 41217557051778419950673894784 := by
  rw [← show ((([(5, 1), (19, 1), (17054500517, 1), (33566862285208493, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_5, prime_fortySixAR_19, prime_fortySixAR_17054500517, prime_fortySixAR_33566862285208493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633696 : Nat.totient 54384276668729824305522633696 = 18125897933512489655484357120 := by
  rw [← show ((([(2, 5), (3, 1), (8263, 1), (45098231, 1), (1520214477104117, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_3, prime_fortySixAR_8263, prime_fortySixAR_45098231, prime_fortySixAR_1520214477104117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633697 : Nat.totient 54384276668729824305522633697 = 54240594778021294611787652064 := by
  rw [← show ((([(419, 1), (3907, 1), (33221246406596460978809, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_419, prime_fortySixAR_3907, prime_fortySixAR_33221246406596460978809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633698 : Nat.totient 54384276668729824305522633698 = 23137419062400175512672780192 := by
  rw [← show ((([(2, 1), (7, 3), (137, 1), (578666943337339323546239, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_7, prime_fortySixAR_137, prime_fortySixAR_578666943337339323546239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633699 : Nat.totient 54384276668729824305522633699 = 32960167678018075336680384000 := by
  rw [← show ((([(3, 2), (11, 1), (549336127966967922278006401, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_3, prime_fortySixAR_11, prime_fortySixAR_549336127966967922278006401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySixAR_54384276668729824305522633700 : Nat.totient 54384276668729824305522633700 = 21752224097205648654195240960 := by
  rw [← show ((([(2, 2), (5, 2), (20129, 1), (53597, 1), (504093009929136949, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729824305522633700 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySixAR_2, prime_fortySixAR_5, prime_fortySixAR_20129, prime_fortySixAR_53597, prime_fortySixAR_504093009929136949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortySixAR : certifiedKill 1 54384276668729824305522633599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortySixAR_54384276668729824305522633600, phi_fortySixAR_54384276668729824305522633601, phi_fortySixAR_54384276668729824305522633602,
    phi_fortySixAR_54384276668729824305522633603, phi_fortySixAR_54384276668729824305522633604, phi_fortySixAR_54384276668729824305522633605,
    phi_fortySixAR_54384276668729824305522633606, phi_fortySixAR_54384276668729824305522633607, phi_fortySixAR_54384276668729824305522633608,
    phi_fortySixAR_54384276668729824305522633609, phi_fortySixAR_54384276668729824305522633610, phi_fortySixAR_54384276668729824305522633611,
    phi_fortySixAR_54384276668729824305522633612, phi_fortySixAR_54384276668729824305522633613, phi_fortySixAR_54384276668729824305522633614,
    phi_fortySixAR_54384276668729824305522633615, phi_fortySixAR_54384276668729824305522633616, phi_fortySixAR_54384276668729824305522633617,
    phi_fortySixAR_54384276668729824305522633618, phi_fortySixAR_54384276668729824305522633619, phi_fortySixAR_54384276668729824305522633620,
    phi_fortySixAR_54384276668729824305522633621, phi_fortySixAR_54384276668729824305522633622, phi_fortySixAR_54384276668729824305522633623,
    phi_fortySixAR_54384276668729824305522633624, phi_fortySixAR_54384276668729824305522633625, phi_fortySixAR_54384276668729824305522633626,
    phi_fortySixAR_54384276668729824305522633627, phi_fortySixAR_54384276668729824305522633628, phi_fortySixAR_54384276668729824305522633629,
    phi_fortySixAR_54384276668729824305522633630, phi_fortySixAR_54384276668729824305522633631, phi_fortySixAR_54384276668729824305522633632,
    phi_fortySixAR_54384276668729824305522633633, phi_fortySixAR_54384276668729824305522633634, phi_fortySixAR_54384276668729824305522633635,
    phi_fortySixAR_54384276668729824305522633636, phi_fortySixAR_54384276668729824305522633637, phi_fortySixAR_54384276668729824305522633638,
    phi_fortySixAR_54384276668729824305522633639, phi_fortySixAR_54384276668729824305522633640, phi_fortySixAR_54384276668729824305522633641,
    phi_fortySixAR_54384276668729824305522633642, phi_fortySixAR_54384276668729824305522633643, phi_fortySixAR_54384276668729824305522633644,
    phi_fortySixAR_54384276668729824305522633645, phi_fortySixAR_54384276668729824305522633646, phi_fortySixAR_54384276668729824305522633647,
    phi_fortySixAR_54384276668729824305522633648, phi_fortySixAR_54384276668729824305522633649, phi_fortySixAR_54384276668729824305522633650,
    phi_fortySixAR_54384276668729824305522633651, phi_fortySixAR_54384276668729824305522633652, phi_fortySixAR_54384276668729824305522633653,
    phi_fortySixAR_54384276668729824305522633654, phi_fortySixAR_54384276668729824305522633655, phi_fortySixAR_54384276668729824305522633656,
    phi_fortySixAR_54384276668729824305522633657, phi_fortySixAR_54384276668729824305522633658, phi_fortySixAR_54384276668729824305522633659,
    phi_fortySixAR_54384276668729824305522633660, phi_fortySixAR_54384276668729824305522633661, phi_fortySixAR_54384276668729824305522633662,
    phi_fortySixAR_54384276668729824305522633663, phi_fortySixAR_54384276668729824305522633664, phi_fortySixAR_54384276668729824305522633665,
    phi_fortySixAR_54384276668729824305522633666, phi_fortySixAR_54384276668729824305522633667, phi_fortySixAR_54384276668729824305522633668,
    phi_fortySixAR_54384276668729824305522633669, phi_fortySixAR_54384276668729824305522633670, phi_fortySixAR_54384276668729824305522633671,
    phi_fortySixAR_54384276668729824305522633672, phi_fortySixAR_54384276668729824305522633673, phi_fortySixAR_54384276668729824305522633674,
    phi_fortySixAR_54384276668729824305522633675, phi_fortySixAR_54384276668729824305522633676, phi_fortySixAR_54384276668729824305522633677,
    phi_fortySixAR_54384276668729824305522633678, phi_fortySixAR_54384276668729824305522633679, phi_fortySixAR_54384276668729824305522633680,
    phi_fortySixAR_54384276668729824305522633681, phi_fortySixAR_54384276668729824305522633682, phi_fortySixAR_54384276668729824305522633683,
    phi_fortySixAR_54384276668729824305522633684, phi_fortySixAR_54384276668729824305522633685, phi_fortySixAR_54384276668729824305522633686,
    phi_fortySixAR_54384276668729824305522633687, phi_fortySixAR_54384276668729824305522633688, phi_fortySixAR_54384276668729824305522633689,
    phi_fortySixAR_54384276668729824305522633690, phi_fortySixAR_54384276668729824305522633691, phi_fortySixAR_54384276668729824305522633692,
    phi_fortySixAR_54384276668729824305522633693, phi_fortySixAR_54384276668729824305522633694, phi_fortySixAR_54384276668729824305522633695,
    phi_fortySixAR_54384276668729824305522633696, phi_fortySixAR_54384276668729824305522633697, phi_fortySixAR_54384276668729824305522633698,
    phi_fortySixAR_54384276668729824305522633699, phi_fortySixAR_54384276668729824305522633700]

end TotientTailPeriodKiller
end Erdos249257
