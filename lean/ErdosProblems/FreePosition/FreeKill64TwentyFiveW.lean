import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentyFiveWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyFiveWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyFiveWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyFiveWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyFiveWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyFiveWFastPow a n * twentyFiveWFastPow a n * a
        else twentyFiveWFastPow a n * twentyFiveWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyFiveW_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentyFiveW_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentyFiveW_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentyFiveW_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentyFiveW_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentyFiveW_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentyFiveW_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentyFiveW_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentyFiveW_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentyFiveW_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentyFiveW_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentyFiveW_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentyFiveW_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentyFiveW_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentyFiveW_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentyFiveW_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentyFiveW_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentyFiveW_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentyFiveW_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentyFiveW_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentyFiveW_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentyFiveW_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentyFiveW_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentyFiveW_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentyFiveW_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentyFiveW_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentyFiveW_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentyFiveW_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentyFiveW_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentyFiveW_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentyFiveW_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentyFiveW_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentyFiveW_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentyFiveW_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentyFiveW_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentyFiveW_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentyFiveW_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentyFiveW_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentyFiveW_167 : Nat.Prime 167 := by norm_num
private theorem prime_twentyFiveW_179 : Nat.Prime 179 := by norm_num
private theorem prime_twentyFiveW_181 : Nat.Prime 181 := by norm_num
private theorem prime_twentyFiveW_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentyFiveW_193 : Nat.Prime 193 := by norm_num
private theorem prime_twentyFiveW_197 : Nat.Prime 197 := by norm_num
private theorem prime_twentyFiveW_199 : Nat.Prime 199 := by norm_num
private theorem prime_twentyFiveW_211 : Nat.Prime 211 := by norm_num
private theorem prime_twentyFiveW_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentyFiveW_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentyFiveW_229 : Nat.Prime 229 := by norm_num
private theorem prime_twentyFiveW_233 : Nat.Prime 233 := by norm_num
private theorem prime_twentyFiveW_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentyFiveW_241 : Nat.Prime 241 := by norm_num
private theorem prime_twentyFiveW_257 : Nat.Prime 257 := by norm_num
private theorem prime_twentyFiveW_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentyFiveW_269 : Nat.Prime 269 := by norm_num
private theorem prime_twentyFiveW_271 : Nat.Prime 271 := by norm_num
private theorem prime_twentyFiveW_277 : Nat.Prime 277 := by norm_num
private theorem prime_twentyFiveW_283 : Nat.Prime 283 := by norm_num
private theorem prime_twentyFiveW_307 : Nat.Prime 307 := by norm_num
private theorem prime_twentyFiveW_317 : Nat.Prime 317 := by norm_num
private theorem prime_twentyFiveW_347 : Nat.Prime 347 := by norm_num
private theorem prime_twentyFiveW_349 : Nat.Prime 349 := by norm_num
private theorem prime_twentyFiveW_353 : Nat.Prime 353 := by norm_num
private theorem prime_twentyFiveW_359 : Nat.Prime 359 := by norm_num
private theorem prime_twentyFiveW_373 : Nat.Prime 373 := by norm_num
private theorem prime_twentyFiveW_383 : Nat.Prime 383 := by norm_num
private theorem prime_twentyFiveW_389 : Nat.Prime 389 := by norm_num
private theorem prime_twentyFiveW_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentyFiveW_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentyFiveW_431 : Nat.Prime 431 := by norm_num
private theorem prime_twentyFiveW_443 : Nat.Prime 443 := by norm_num
private theorem prime_twentyFiveW_449 : Nat.Prime 449 := by norm_num
private theorem prime_twentyFiveW_463 : Nat.Prime 463 := by norm_num
private theorem prime_twentyFiveW_479 : Nat.Prime 479 := by norm_num
private theorem prime_twentyFiveW_509 : Nat.Prime 509 := by norm_num
private theorem prime_twentyFiveW_521 : Nat.Prime 521 := by norm_num
private theorem prime_twentyFiveW_541 : Nat.Prime 541 := by norm_num
private theorem prime_twentyFiveW_557 : Nat.Prime 557 := by norm_num
private theorem prime_twentyFiveW_563 : Nat.Prime 563 := by norm_num
private theorem prime_twentyFiveW_569 : Nat.Prime 569 := by norm_num
private theorem prime_twentyFiveW_587 : Nat.Prime 587 := by norm_num
private theorem prime_twentyFiveW_593 : Nat.Prime 593 := by norm_num
private theorem prime_twentyFiveW_599 : Nat.Prime 599 := by norm_num
private theorem prime_twentyFiveW_607 : Nat.Prime 607 := by norm_num
private theorem prime_twentyFiveW_613 : Nat.Prime 613 := by norm_num
private theorem prime_twentyFiveW_619 : Nat.Prime 619 := by norm_num
private theorem prime_twentyFiveW_643 : Nat.Prime 643 := by norm_num
private theorem prime_twentyFiveW_701 : Nat.Prime 701 := by norm_num
private theorem prime_twentyFiveW_733 : Nat.Prime 733 := by norm_num
private theorem prime_twentyFiveW_757 : Nat.Prime 757 := by norm_num
private theorem prime_twentyFiveW_761 : Nat.Prime 761 := by norm_num
private theorem prime_twentyFiveW_823 : Nat.Prime 823 := by norm_num
private theorem prime_twentyFiveW_863 : Nat.Prime 863 := by norm_num
private theorem prime_twentyFiveW_883 : Nat.Prime 883 := by norm_num
private theorem prime_twentyFiveW_937 : Nat.Prime 937 := by norm_num
private theorem prime_twentyFiveW_941 : Nat.Prime 941 := by norm_num
private theorem prime_twentyFiveW_977 : Nat.Prime 977 := by norm_num
private theorem prime_twentyFiveW_983 : Nat.Prime 983 := by norm_num
private theorem prime_twentyFiveW_997 : Nat.Prime 997 := by norm_num
private theorem prime_twentyFiveW_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_twentyFiveW_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_twentyFiveW_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_twentyFiveW_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_twentyFiveW_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_twentyFiveW_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_twentyFiveW_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_twentyFiveW_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_twentyFiveW_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_twentyFiveW_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_twentyFiveW_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_twentyFiveW_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_twentyFiveW_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twentyFiveW_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_twentyFiveW_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_twentyFiveW_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_twentyFiveW_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_twentyFiveW_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_twentyFiveW_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_twentyFiveW_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_twentyFiveW_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_twentyFiveW_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_twentyFiveW_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_twentyFiveW_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_twentyFiveW_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_twentyFiveW_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_twentyFiveW_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_twentyFiveW_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_twentyFiveW_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_twentyFiveW_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_twentyFiveW_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_twentyFiveW_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_twentyFiveW_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_twentyFiveW_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentyFiveW_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_twentyFiveW_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_twentyFiveW_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_twentyFiveW_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_twentyFiveW_3359 : Nat.Prime 3359 := by norm_num
private theorem prime_twentyFiveW_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_twentyFiveW_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_twentyFiveW_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_twentyFiveW_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_twentyFiveW_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_twentyFiveW_4133 : Nat.Prime 4133 := by norm_num
private theorem prime_twentyFiveW_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_twentyFiveW_4157 : Nat.Prime 4157 := by norm_num
private theorem prime_twentyFiveW_4201 : Nat.Prime 4201 := by norm_num
private theorem prime_twentyFiveW_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_twentyFiveW_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_twentyFiveW_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_twentyFiveW_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_twentyFiveW_4999 : Nat.Prime 4999 := by norm_num
private theorem prime_twentyFiveW_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentyFiveW_5039 : Nat.Prime 5039 := by norm_num
private theorem prime_twentyFiveW_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_twentyFiveW_5431 : Nat.Prime 5431 := by norm_num
private theorem prime_twentyFiveW_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_twentyFiveW_5623 : Nat.Prime 5623 := by norm_num
private theorem prime_twentyFiveW_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_twentyFiveW_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_twentyFiveW_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_twentyFiveW_5939 : Nat.Prime 5939 := by norm_num
private theorem prime_twentyFiveW_6427 : Nat.Prime 6427 := by norm_num
private theorem prime_twentyFiveW_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_twentyFiveW_6607 : Nat.Prime 6607 := by norm_num
private theorem prime_twentyFiveW_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentyFiveW_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_twentyFiveW_6871 : Nat.Prime 6871 := by norm_num
private theorem prime_twentyFiveW_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_twentyFiveW_7333 : Nat.Prime 7333 := by norm_num
private theorem prime_twentyFiveW_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_twentyFiveW_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_twentyFiveW_7919 : Nat.Prime 7919 := by norm_num
private theorem prime_twentyFiveW_8059 : Nat.Prime 8059 := by norm_num
private theorem prime_twentyFiveW_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_twentyFiveW_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_twentyFiveW_8387 : Nat.Prime 8387 := by norm_num
private theorem prime_twentyFiveW_8647 : Nat.Prime 8647 := by norm_num
private theorem prime_twentyFiveW_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_twentyFiveW_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_twentyFiveW_9533 : Nat.Prime 9533 := by norm_num
private theorem prime_twentyFiveW_9781 : Nat.Prime 9781 := by norm_num
private theorem prime_twentyFiveW_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_twentyFiveW_10163 : Nat.Prime 10163 := by norm_num
private theorem prime_twentyFiveW_10169 : Nat.Prime 10169 := by norm_num
private theorem prime_twentyFiveW_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_twentyFiveW_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_twentyFiveW_12109 : Nat.Prime 12109 := by norm_num
private theorem prime_twentyFiveW_12149 : Nat.Prime 12149 := by norm_num
private theorem prime_twentyFiveW_12377 : Nat.Prime 12377 := by norm_num
private theorem prime_twentyFiveW_12601 : Nat.Prime 12601 := by norm_num
private theorem prime_twentyFiveW_12791 : Nat.Prime 12791 := by norm_num
private theorem prime_twentyFiveW_12809 : Nat.Prime 12809 := by norm_num
private theorem prime_twentyFiveW_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_twentyFiveW_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_twentyFiveW_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_twentyFiveW_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_twentyFiveW_14033 : Nat.Prime 14033 := by norm_num
private theorem prime_twentyFiveW_14447 : Nat.Prime 14447 := by norm_num
private theorem prime_twentyFiveW_14591 : Nat.Prime 14591 := by norm_num
private theorem prime_twentyFiveW_14783 : Nat.Prime 14783 := by norm_num
private theorem prime_twentyFiveW_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_twentyFiveW_15451 : Nat.Prime 15451 := by norm_num
private theorem prime_twentyFiveW_15937 : Nat.Prime 15937 := by norm_num
private theorem prime_twentyFiveW_16417 : Nat.Prime 16417 := by norm_num
private theorem prime_twentyFiveW_16567 : Nat.Prime 16567 := by norm_num
private theorem prime_twentyFiveW_17027 : Nat.Prime 17027 := by norm_num
private theorem prime_twentyFiveW_17209 : Nat.Prime 17209 := by norm_num
private theorem prime_twentyFiveW_17489 : Nat.Prime 17489 := by norm_num
private theorem prime_twentyFiveW_18899 : Nat.Prime 18899 := by norm_num
private theorem prime_twentyFiveW_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_twentyFiveW_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_twentyFiveW_19961 : Nat.Prime 19961 := by norm_num
private theorem prime_twentyFiveW_20231 : Nat.Prime 20231 := by norm_num
private theorem prime_twentyFiveW_20431 : Nat.Prime 20431 := by norm_num
private theorem prime_twentyFiveW_20983 : Nat.Prime 20983 := by norm_num
private theorem prime_twentyFiveW_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_twentyFiveW_21401 : Nat.Prime 21401 := by norm_num
private theorem prime_twentyFiveW_22697 : Nat.Prime 22697 := by norm_num
private theorem prime_twentyFiveW_25411 : Nat.Prime 25411 := by norm_num
private theorem prime_twentyFiveW_27031 : Nat.Prime 27031 := by norm_num
private theorem prime_twentyFiveW_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_twentyFiveW_30097 : Nat.Prime 30097 := by norm_num
private theorem prime_twentyFiveW_30181 : Nat.Prime 30181 := by norm_num
private theorem prime_twentyFiveW_31531 : Nat.Prime 31531 := by norm_num
private theorem prime_twentyFiveW_31741 : Nat.Prime 31741 := by norm_num
private theorem prime_twentyFiveW_32491 : Nat.Prime 32491 := by norm_num
private theorem prime_twentyFiveW_32497 : Nat.Prime 32497 := by norm_num
private theorem prime_twentyFiveW_32561 : Nat.Prime 32561 := by norm_num
private theorem prime_twentyFiveW_33301 : Nat.Prime 33301 := by norm_num
private theorem prime_twentyFiveW_33809 : Nat.Prime 33809 := by norm_num
private theorem prime_twentyFiveW_34963 : Nat.Prime 34963 := by norm_num
private theorem prime_twentyFiveW_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentyFiveW_36013 : Nat.Prime 36013 := by norm_num
private theorem prime_twentyFiveW_36997 : Nat.Prime 36997 := by norm_num
private theorem prime_twentyFiveW_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_twentyFiveW_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentyFiveW_38891 : Nat.Prime 38891 := by norm_num
private theorem prime_twentyFiveW_39103 : Nat.Prime 39103 := by norm_num
private theorem prime_twentyFiveW_39209 : Nat.Prime 39209 := by norm_num
private theorem prime_twentyFiveW_40093 : Nat.Prime 40093 := by norm_num
private theorem prime_twentyFiveW_41203 : Nat.Prime 41203 := by norm_num
private theorem prime_twentyFiveW_43223 : Nat.Prime 43223 := by norm_num
private theorem prime_twentyFiveW_45697 : Nat.Prime 45697 := by norm_num
private theorem prime_twentyFiveW_46219 : Nat.Prime 46219 := by norm_num
private theorem prime_twentyFiveW_47161 : Nat.Prime 47161 := by norm_num
private theorem prime_twentyFiveW_47431 : Nat.Prime 47431 := by norm_num
private theorem prime_twentyFiveW_49009 : Nat.Prime 49009 := by norm_num
private theorem prime_twentyFiveW_53951 : Nat.Prime 53951 := by norm_num
private theorem prime_twentyFiveW_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_twentyFiveW_56923 : Nat.Prime 56923 := by norm_num
private theorem prime_twentyFiveW_58789 : Nat.Prime 58789 := by norm_num
private theorem prime_twentyFiveW_58909 : Nat.Prime 58909 := by norm_num
private theorem prime_twentyFiveW_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentyFiveW_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_twentyFiveW_65579 : Nat.Prime 65579 := by norm_num
private theorem prime_twentyFiveW_66533 : Nat.Prime 66533 := by norm_num
private theorem prime_twentyFiveW_67537 : Nat.Prime 67537 := by norm_num
private theorem prime_twentyFiveW_68897 : Nat.Prime 68897 := by norm_num
private theorem prime_twentyFiveW_70249 : Nat.Prime 70249 := by norm_num
private theorem prime_twentyFiveW_71711 : Nat.Prime 71711 := by norm_num
private theorem prime_twentyFiveW_77699 : Nat.Prime 77699 := by norm_num
private theorem prime_twentyFiveW_78041 : Nat.Prime 78041 := by norm_num
private theorem prime_twentyFiveW_79241 : Nat.Prime 79241 := by norm_num
private theorem prime_twentyFiveW_81013 : Nat.Prime 81013 := by norm_num
private theorem prime_twentyFiveW_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_twentyFiveW_93287 : Nat.Prime 93287 := by norm_num
private theorem prime_twentyFiveW_94421 : Nat.Prime 94421 := by norm_num
private theorem prime_twentyFiveW_99611 : Nat.Prime 99611 := by norm_num
private theorem prime_twentyFiveW_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_twentyFiveW_102161 : Nat.Prime 102161 := by norm_num
private theorem prime_twentyFiveW_104323 : Nat.Prime 104323 := by norm_num
private theorem prime_twentyFiveW_106759 : Nat.Prime 106759 := by norm_num
private theorem prime_twentyFiveW_109829 : Nat.Prime 109829 := by norm_num
private theorem prime_twentyFiveW_114859 : Nat.Prime 114859 := by norm_num
private theorem prime_twentyFiveW_116687 : Nat.Prime 116687 := by norm_num
private theorem prime_twentyFiveW_124739 : Nat.Prime 124739 := by norm_num
private theorem prime_twentyFiveW_128467 : Nat.Prime 128467 := by norm_num
private theorem prime_twentyFiveW_134593 : Nat.Prime 134593 := by norm_num
private theorem prime_twentyFiveW_138403 : Nat.Prime 138403 := by norm_num
private theorem prime_twentyFiveW_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_twentyFiveW_143687 : Nat.Prime 143687 := by norm_num
private theorem prime_twentyFiveW_156521 : Nat.Prime 156521 := by norm_num
private theorem prime_twentyFiveW_159521 : Nat.Prime 159521 := by norm_num
private theorem prime_twentyFiveW_160423 : Nat.Prime 160423 := by norm_num
private theorem prime_twentyFiveW_163483 : Nat.Prime 163483 := by norm_num
private theorem prime_twentyFiveW_169067 : Nat.Prime 169067 := by norm_num
private theorem prime_twentyFiveW_170447 : Nat.Prime 170447 := by norm_num
private theorem prime_twentyFiveW_179999 : Nat.Prime 179999 := by norm_num
private theorem prime_twentyFiveW_191657 : Nat.Prime 191657 := by norm_num
private theorem prime_twentyFiveW_205847 : Nat.Prime 205847 := by norm_num
private theorem prime_twentyFiveW_211441 : Nat.Prime 211441 := by norm_num
private theorem prime_twentyFiveW_212453 : Nat.Prime 212453 := by norm_num
private theorem prime_twentyFiveW_242819 : Nat.Prime 242819 := by norm_num
private theorem prime_twentyFiveW_245437 : Nat.Prime 245437 := by norm_num
private theorem prime_twentyFiveW_254437 : Nat.Prime 254437 := by norm_num
private theorem prime_twentyFiveW_276439 : Nat.Prime 276439 := by norm_num
private theorem prime_twentyFiveW_290767 : Nat.Prime 290767 := by norm_num
private theorem prime_twentyFiveW_295219 : Nat.Prime 295219 := by norm_num
private theorem prime_twentyFiveW_304049 : Nat.Prime 304049 := by norm_num
private theorem prime_twentyFiveW_320591 : Nat.Prime 320591 := by norm_num
private theorem prime_twentyFiveW_329027 : Nat.Prime 329027 := by norm_num
private theorem prime_twentyFiveW_334183 : Nat.Prime 334183 := by norm_num
private theorem prime_twentyFiveW_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_twentyFiveW_384497 : Nat.Prime 384497 := by norm_num
private theorem prime_twentyFiveW_401417 : Nat.Prime 401417 := by norm_num
private theorem prime_twentyFiveW_412567 : Nat.Prime 412567 := by norm_num
private theorem prime_twentyFiveW_450707 : Nat.Prime 450707 := by norm_num
private theorem prime_twentyFiveW_475073 : Nat.Prime 475073 := by norm_num
private theorem prime_twentyFiveW_475721 : Nat.Prime 475721 := by norm_num
private theorem prime_twentyFiveW_504857 : Nat.Prime 504857 := by norm_num
private theorem prime_twentyFiveW_510683 : Nat.Prime 510683 := by norm_num
private theorem prime_twentyFiveW_512503 : Nat.Prime 512503 := by norm_num
private theorem prime_twentyFiveW_512713 : Nat.Prime 512713 := by norm_num
private theorem prime_twentyFiveW_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_twentyFiveW_589507 : Nat.Prime 589507 := by norm_num
private theorem prime_twentyFiveW_595571 : Nat.Prime 595571 := by norm_num
private theorem prime_twentyFiveW_621799 : Nat.Prime 621799 := by norm_num
private theorem prime_twentyFiveW_625199 : Nat.Prime 625199 := by norm_num
private theorem prime_twentyFiveW_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_twentyFiveW_695239 : Nat.Prime 695239 := by norm_num
private theorem prime_twentyFiveW_698039 : Nat.Prime 698039 := by norm_num
private theorem prime_twentyFiveW_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_twentyFiveW_835591 : Nat.Prime 835591 := by norm_num
private theorem prime_twentyFiveW_837779 : Nat.Prime 837779 := by norm_num
private theorem prime_twentyFiveW_857663 : Nat.Prime 857663 := by norm_num
private theorem prime_twentyFiveW_899233 : Nat.Prime 899233 := by norm_num
private theorem prime_twentyFiveW_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_twentyFiveW_939487 : Nat.Prime 939487 := by norm_num
private theorem prime_twentyFiveW_1087159 : Nat.Prime 1087159 := by norm_num
private theorem prime_twentyFiveW_1109609 : Nat.Prime 1109609 := by norm_num
private theorem prime_twentyFiveW_1171811 : Nat.Prime 1171811 := by norm_num
private theorem prime_twentyFiveW_1200377 : Nat.Prime 1200377 := by norm_num
private theorem prime_twentyFiveW_1236073 : Nat.Prime 1236073 := by norm_num
private theorem prime_twentyFiveW_1273889 : Nat.Prime 1273889 := by norm_num
private theorem prime_twentyFiveW_1292237 : Nat.Prime 1292237 := by norm_num
private theorem prime_twentyFiveW_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_twentyFiveW_1467937 : Nat.Prime 1467937 := by norm_num
private theorem prime_twentyFiveW_1503311 : Nat.Prime 1503311 := by norm_num
private theorem prime_twentyFiveW_1516763 : Nat.Prime 1516763 := by norm_num
private theorem prime_twentyFiveW_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_twentyFiveW_1673183 : Nat.Prime 1673183 := by norm_num
private theorem prime_twentyFiveW_1791037 : Nat.Prime 1791037 := by norm_num
private theorem prime_twentyFiveW_1812449 : Nat.Prime 1812449 := by norm_num
private theorem prime_twentyFiveW_2098079 : Nat.Prime 2098079 := by norm_num
private theorem prime_twentyFiveW_2122619 : Nat.Prime 2122619 := by norm_num
private theorem prime_twentyFiveW_2183227 : Nat.Prime 2183227 := by norm_num
private theorem prime_twentyFiveW_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_twentyFiveW_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_twentyFiveW_2438833 : Nat.Prime 2438833 := by norm_num
private theorem prime_twentyFiveW_2518211 : Nat.Prime 2518211 := by norm_num
private theorem prime_twentyFiveW_2596889 : Nat.Prime 2596889 := by norm_num
private theorem prime_twentyFiveW_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_twentyFiveW_3173579 : Nat.Prime 3173579 := by norm_num
private theorem prime_twentyFiveW_3421567 : Nat.Prime 3421567 := by norm_num
private theorem prime_twentyFiveW_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_twentyFiveW_3534683 : Nat.Prime 3534683 := by norm_num
private theorem prime_twentyFiveW_3834547 : Nat.Prime 3834547 := by norm_num
private theorem prime_twentyFiveW_3940969 : Nat.Prime 3940969 := by norm_num
private theorem prime_twentyFiveW_4247039 : Nat.Prime 4247039 := by norm_num
private theorem prime_twentyFiveW_4719079 : Nat.Prime 4719079 := by norm_num
private theorem prime_twentyFiveW_4801033 : Nat.Prime 4801033 := by norm_num
private theorem prime_twentyFiveW_5075167 : Nat.Prime 5075167 := by norm_num
private theorem prime_twentyFiveW_5358737 : Nat.Prime 5358737 := by norm_num
private theorem prime_twentyFiveW_5592011 : Nat.Prime 5592011 := by norm_num
private theorem prime_twentyFiveW_5845319 : Nat.Prime 5845319 := by norm_num
private theorem prime_twentyFiveW_6215987 : Nat.Prime 6215987 := by norm_num
private theorem prime_twentyFiveW_6302249 : Nat.Prime 6302249 := by norm_num
private theorem prime_twentyFiveW_6775583 : Nat.Prime 6775583 := by norm_num
private theorem prime_twentyFiveW_6952579 : Nat.Prime 6952579 := by norm_num
private theorem prime_twentyFiveW_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentyFiveW_7268321 : Nat.Prime 7268321 := by norm_num
private theorem prime_twentyFiveW_7294097 : Nat.Prime 7294097 := by norm_num
private theorem prime_twentyFiveW_7447087 : Nat.Prime 7447087 := by norm_num
private theorem prime_twentyFiveW_7929133 : Nat.Prime 7929133 := by norm_num
private theorem prime_twentyFiveW_8408039 : Nat.Prime 8408039 := by norm_num
private theorem prime_twentyFiveW_8590367 : Nat.Prime 8590367 := by norm_num
private theorem prime_twentyFiveW_8809049 : Nat.Prime 8809049 := by norm_num
private theorem prime_twentyFiveW_8903891 : Nat.Prime 8903891 := by norm_num
private theorem prime_twentyFiveW_9156887 : Nat.Prime 9156887 := by norm_num
private theorem prime_twentyFiveW_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_twentyFiveW_9836257 : Nat.Prime 9836257 := by norm_num
private theorem prime_twentyFiveW_9939247 : Nat.Prime 9939247 := by norm_num
private theorem prime_twentyFiveW_11577857 : Nat.Prime 11577857 := by norm_num
private theorem prime_twentyFiveW_11825117 : Nat.Prime 11825117 := by norm_num
private theorem prime_twentyFiveW_12128443 : Nat.Prime 12128443 := by norm_num
private theorem prime_twentyFiveW_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_twentyFiveW_14588891 : Nat.Prime 14588891 := by norm_num
private theorem prime_twentyFiveW_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_twentyFiveW_14861029 : Nat.Prime 14861029 := by norm_num
private theorem prime_twentyFiveW_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_twentyFiveW_15610789 : Nat.Prime 15610789 := by norm_num
private theorem prime_twentyFiveW_16230497 : Nat.Prime 16230497 := by norm_num
private theorem prime_twentyFiveW_16937033 : Nat.Prime 16937033 := by norm_num
private theorem prime_twentyFiveW_20488627 : Nat.Prime 20488627 := by norm_num
private theorem prime_twentyFiveW_21268679 : Nat.Prime 21268679 := by norm_num
private theorem prime_twentyFiveW_21421693 : Nat.Prime 21421693 := by norm_num
private theorem prime_twentyFiveW_23622671 : Nat.Prime 23622671 := by norm_num
private theorem prime_twentyFiveW_26190893 : Nat.Prime 26190893 := by norm_num

private theorem prime_twentyFiveW_33064529 : Nat.Prime 33064529 := by
  apply lucas_primality 33064529 (3 : ZMod 33064529)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (295219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (295219, 1)] : List FactorBlock).map factorBlockValue).prod) = 33064529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_295219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33064529) ^ 16532264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 33064529) ^ 4723504 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 33064529) ^ 112 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_33371699 : Nat.Prime 33371699 := by
  apply lucas_primality 33371699 (6 : ZMod 33371699)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (59, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (59, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) = 33371699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 33371699) ^ 16685849 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371699) ^ 776086 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371699) ^ 565622 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371699) ^ 5074 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_33915461 : Nat.Prime 33915461 := by
  apply lucas_primality 33915461 (2 : ZMod 33915461)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (20431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (20431, 1)] : List FactorBlock).map factorBlockValue).prod) = 33915461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_83
      · exact prime_twentyFiveW_20431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33915461) ^ 16957730 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33915461) ^ 6783092 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33915461) ^ 408620 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33915461) ^ 1660 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_39409691 : Nat.Prime 39409691 := by
  apply lucas_primality 39409691 (2 : ZMod 39409691)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3940969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3940969, 1)] : List FactorBlock).map factorBlockValue).prod) = 39409691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_3940969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39409691) ^ 19704845 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39409691) ^ 7881938 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39409691) ^ 10 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_40653499 : Nat.Prime 40653499 := by
  apply lucas_primality 40653499 (2 : ZMod 40653499)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6775583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6775583, 1)] : List FactorBlock).map factorBlockValue).prod) = 40653499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_6775583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40653499) ^ 20326749 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40653499) ^ 13551166 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40653499) ^ 6 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_42416197 : Nat.Prime 42416197 := by
  apply lucas_primality 42416197 (2 : ZMod 42416197)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3534683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3534683, 1)] : List FactorBlock).map factorBlockValue).prod) = 42416197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_3534683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42416197) ^ 21208098 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 42416197) ^ 14138732 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 42416197) ^ 12 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_48439799 : Nat.Prime 48439799 := by
  apply lucas_primality 48439799 (11 : ZMod 48439799)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (79, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (79, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 48439799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 48439799) ^ 24219899 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 48439799) ^ 4403618 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 48439799) ^ 1030634 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 48439799) ^ 613162 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 48439799) ^ 81686 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_51050897 : Nat.Prime 51050897 := by
  apply lucas_primality 51050897 (3 : ZMod 51050897)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (245437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (245437, 1)] : List FactorBlock).map factorBlockValue).prod) = 51050897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_245437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 51050897) ^ 25525448 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 51050897) ^ 3926992 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 51050897) ^ 208 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_53955521 : Nat.Prime 53955521 := by
  apply lucas_primality 53955521 (3 : ZMod 53955521)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (103, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (103, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 53955521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_103
      · exact prime_twentyFiveW_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53955521) ^ 26977760 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 53955521) ^ 10791104 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 53955521) ^ 523840 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 53955521) ^ 32960 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_54941323 : Nat.Prime 54941323 := by
  apply lucas_primality 54941323 (2 : ZMod 54941323)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9156887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9156887, 1)] : List FactorBlock).map factorBlockValue).prod) = 54941323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_9156887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54941323) ^ 27470661 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54941323) ^ 18313774 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54941323) ^ 6 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_55149007 : Nat.Prime 55149007 := by
  apply lucas_primality 55149007 (3 : ZMod 55149007)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (835591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (835591, 1)] : List FactorBlock).map factorBlockValue).prod) = 55149007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_835591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55149007) ^ 27574503 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 55149007) ^ 18383002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 55149007) ^ 5013546 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 55149007) ^ 66 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_56492851 : Nat.Prime 56492851 := by
  apply lucas_primality 56492851 (3 : ZMod 56492851)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (12149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (12149, 1)] : List FactorBlock).map factorBlockValue).prod) = 56492851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_12149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56492851) ^ 28246425 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 18830950 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 11298570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 1822350 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 4650 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_56773939 : Nat.Prime 56773939 := by
  apply lucas_primality 56773939 (2 : ZMod 56773939)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (29, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (29, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 56773939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56773939) ^ 28386969 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56773939) ^ 18924646 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56773939) ^ 4367226 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56773939) ^ 2988102 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56773939) ^ 1957722 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56773939) ^ 42978 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_62181967 : Nat.Prime 62181967 := by
  apply lucas_primality 62181967 (3 : ZMod 62181967)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (134593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (134593, 1)] : List FactorBlock).map factorBlockValue).prod) = 62181967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_134593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62181967) ^ 31090983 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62181967) ^ 20727322 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62181967) ^ 8883138 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62181967) ^ 5652906 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 62181967) ^ 462 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_76071361 : Nat.Prime 76071361 := by
  apply lucas_primality 76071361 (13 : ZMod 76071361)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (79241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (79241, 1)] : List FactorBlock).map factorBlockValue).prod) = 76071361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_79241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 76071361) ^ 38035680 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 76071361) ^ 25357120 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 76071361) ^ 15214272 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 76071361) ^ 960 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_78812813 : Nat.Prime 78812813 := by
  apply lucas_primality 78812813 (3 : ZMod 78812813)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (23, 1), (37, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (23, 1), (37, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 78812813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78812813) ^ 39406406 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 78812813) ^ 6062524 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 78812813) ^ 3426644 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 78812813) ^ 2130076 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 78812813) ^ 575276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_84688159 : Nat.Prime 84688159 := by
  apply lucas_primality 84688159 (3 : ZMod 84688159)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (373, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (373, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 84688159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_373
      · exact prime_twentyFiveW_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 84688159) ^ 42344079 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 84688159) ^ 28229386 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 84688159) ^ 1072002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 84688159) ^ 227046 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 84688159) ^ 176802 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_91285969 : Nat.Prime 91285969 := by
  apply lucas_primality 91285969 (7 : ZMod 91285969)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (65579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (65579, 1)] : List FactorBlock).map factorBlockValue).prod) = 91285969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_65579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91285969) ^ 45642984 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91285969) ^ 30428656 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91285969) ^ 3147792 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91285969) ^ 1392 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_91721767 : Nat.Prime 91721767 := by
  apply lucas_primality 91721767 (5 : ZMod 91721767)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (899233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (899233, 1)] : List FactorBlock).map factorBlockValue).prod) = 91721767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_899233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91721767) ^ 45860883 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 91721767) ^ 30573922 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 91721767) ^ 5395398 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 91721767) ^ 102 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_105040643 : Nat.Prime 105040643 := by
  apply lucas_primality 105040643 (2 : ZMod 105040643)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (397, 1), (18899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (397, 1), (18899, 1)] : List FactorBlock).map factorBlockValue).prod) = 105040643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_397
      · exact prime_twentyFiveW_18899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105040643) ^ 52520321 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 105040643) ^ 15005806 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 105040643) ^ 264586 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 105040643) ^ 5558 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_105602689 : Nat.Prime 105602689 := by
  apply lucas_primality 105602689 (21 : ZMod 105602689)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (29, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (29, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 105602689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 105602689) ^ 52801344 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 35200896 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 3641472 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 968832 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_114293099 : Nat.Prime 114293099 := by
  apply lucas_primality 114293099 (2 : ZMod 114293099)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5623, 1), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5623, 1), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) = 114293099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5623
      · exact prime_twentyFiveW_10163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 114293099) ^ 57146549 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 114293099) ^ 20326 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 114293099) ^ 11246 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_129334193 : Nat.Prime 129334193 := by
  apply lucas_primality 129334193 (3 : ZMod 129334193)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (621799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (621799, 1)] : List FactorBlock).map factorBlockValue).prod) = 129334193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_621799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129334193) ^ 64667096 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 129334193) ^ 9948784 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 129334193) ^ 208 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_136344823 : Nat.Prime 136344823 := by
  apply lucas_primality 136344823 (6 : ZMod 136344823)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (163483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (163483, 1)] : List FactorBlock).map factorBlockValue).prod) = 136344823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_139
      · exact prime_twentyFiveW_163483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 136344823) ^ 68172411 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 136344823) ^ 45448274 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 136344823) ^ 980898 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 136344823) ^ 834 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_144600413 : Nat.Prime 144600413 := by
  apply lucas_primality 144600413 (2 : ZMod 144600413)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (269, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (269, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144600413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_269
      · exact prime_twentyFiveW_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144600413) ^ 72300206 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 144600413) ^ 13145492 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 144600413) ^ 7610548 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 144600413) ^ 537548 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 144600413) ^ 224884 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_149650877 : Nat.Prime 149650877 := by
  apply lucas_primality 149650877 (2 : ZMod 149650877)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (512503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (512503, 1)] : List FactorBlock).map factorBlockValue).prod) = 149650877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_73
      · exact prime_twentyFiveW_512503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 149650877) ^ 74825438 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 149650877) ^ 2050012 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 149650877) ^ 292 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_152559443 : Nat.Prime 152559443 := by
  apply lucas_primality 152559443 (5 : ZMod 152559443)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (41, 1), (43, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (41, 1), (43, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 152559443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 152559443) ^ 76279721 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 21794206 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 3720962 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 3547894 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 172774 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_193301777 : Nat.Prime 193301777 := by
  apply lucas_primality 193301777 (3 : ZMod 193301777)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) = 193301777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_431
      · exact prime_twentyFiveW_28031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193301777) ^ 96650888 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 448496 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 6896 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_214075307 : Nat.Prime 214075307 := by
  apply lucas_primality 214075307 (2 : ZMod 214075307)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (79, 1), (58909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (79, 1), (58909, 1)] : List FactorBlock).map factorBlockValue).prod) = 214075307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_58909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 214075307) ^ 107037653 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 214075307) ^ 9307622 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 214075307) ^ 2709814 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 214075307) ^ 3634 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_231479233 : Nat.Prime 231479233 := by
  apply lucas_primality 231479233 (5 : ZMod 231479233)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (31, 1), (38891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (31, 1), (38891, 1)] : List FactorBlock).map factorBlockValue).prod) = 231479233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_38891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 231479233) ^ 115739616 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 231479233) ^ 77159744 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 231479233) ^ 7467072 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 231479233) ^ 5952 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_97
      · exact prime_twentyFiveW_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_248528221 : Nat.Prime 248528221 := by
  apply lucas_primality 248528221 (10 : ZMod 248528221)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1747, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1747, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 248528221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_1747
      · exact prime_twentyFiveW_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 248528221) ^ 124264110 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 82842740 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 49705644 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 142260 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 104820 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_266338661 : Nat.Prime 266338661 := by
  apply lucas_primality 266338661 (10 : ZMod 266338661)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (17, 1), (47, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (17, 1), (47, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) = 266338661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_2381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 266338661) ^ 133169330 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 53267732 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 38048380 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 15666980 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 5666780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 111860 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_269471693 : Nat.Prime 269471693 := by
  apply lucas_primality 269471693 (2 : ZMod 269471693)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 2), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 2), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) = 269471693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_33301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269471693) ^ 134735846 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 38495956 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 15851276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 8092 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_275415197 : Nat.Prime 275415197 := by
  apply lucas_primality 275415197 (2 : ZMod 275415197)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (9836257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (9836257, 1)] : List FactorBlock).map factorBlockValue).prod) = 275415197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_9836257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 275415197) ^ 137707598 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 275415197) ^ 39345028 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 275415197) ^ 28 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_342746533 : Nat.Prime 342746533 := by
  apply lucas_primality 342746533 (2 : ZMod 342746533)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (3173579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (3173579, 1)] : List FactorBlock).map factorBlockValue).prod) = 342746533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_3173579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 342746533) ^ 171373266 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 342746533) ^ 114248844 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 342746533) ^ 108 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_360933317 : Nat.Prime 360933317 := by
  apply lucas_primality 360933317 (2 : ZMod 360933317)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (1236073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (1236073, 1)] : List FactorBlock).map factorBlockValue).prod) = 360933317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_73
      · exact prime_twentyFiveW_1236073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 360933317) ^ 180466658 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 360933317) ^ 4944292 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 360933317) ^ 292 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_410133851 : Nat.Prime 410133851 := by
  apply lucas_primality 410133851 (2 : ZMod 410133851)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1171811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1171811, 1)] : List FactorBlock).map factorBlockValue).prod) = 410133851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1171811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 410133851) ^ 205066925 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 82026770 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 58590550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 350 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_414430283 : Nat.Prime 414430283 := by
  apply lucas_primality 414430283 (2 : ZMod 414430283)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1483, 1), (19961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1483, 1), (19961, 1)] : List FactorBlock).map factorBlockValue).prod) = 414430283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1483
      · exact prime_twentyFiveW_19961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 414430283) ^ 207215141 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 59204326 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 279454 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 20762 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_416413469 : Nat.Prime 416413469 := by
  apply lucas_primality 416413469 (2 : ZMod 416413469)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1511, 1), (68897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1511, 1), (68897, 1)] : List FactorBlock).map factorBlockValue).prod) = 416413469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_1511
      · exact prime_twentyFiveW_68897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 416413469) ^ 208206734 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 416413469) ^ 275588 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 416413469) ^ 6044 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_422410757 : Nat.Prime 422410757 := by
  apply lucas_primality 422410757 (2 : ZMod 422410757)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (105602689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (105602689, 1)] : List FactorBlock).map factorBlockValue).prod) = 422410757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_105602689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 422410757) ^ 211205378 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 422410757) ^ 4 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_423505781 : Nat.Prime 423505781 := by
  apply lucas_primality 423505781 (2 : ZMod 423505781)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (449, 1), (47161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (449, 1), (47161, 1)] : List FactorBlock).map factorBlockValue).prod) = 423505781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_449
      · exact prime_twentyFiveW_47161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 423505781) ^ 211752890 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 423505781) ^ 84701156 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 423505781) ^ 943220 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 423505781) ^ 8980 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_438217711 : Nat.Prime 438217711 := by
  apply lucas_primality 438217711 (14 : ZMod 438217711)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109829, 1)] : List FactorBlock).map factorBlockValue).prod) = 438217711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_109829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 438217711) ^ 219108855 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 146072570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 87643542 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 62602530 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 23064090 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 3990 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_522823519 : Nat.Prime 522823519 := by
  apply lucas_primality 522823519 (6 : ZMod 522823519)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) = 522823519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_73
      · exact prime_twentyFiveW_18947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522823519) ^ 261411759 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 174274506 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 74689074 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 7161966 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 27594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_526321871 : Nat.Prime 526321871 := by
  apply lucas_primality 526321871 (11 : ZMod 526321871)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (106759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (106759, 1)] : List FactorBlock).map factorBlockValue).prod) = 526321871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_106759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 526321871) ^ 263160935 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 526321871) ^ 105264374 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 526321871) ^ 30960110 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 526321871) ^ 18149030 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 526321871) ^ 4930 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_576799859 : Nat.Prime 576799859 := by
  apply lucas_primality 576799859 (2 : ZMod 576799859)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (863, 1), (334183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (863, 1), (334183, 1)] : List FactorBlock).map factorBlockValue).prod) = 576799859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_863
      · exact prime_twentyFiveW_334183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 576799859) ^ 288399929 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 576799859) ^ 668366 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 576799859) ^ 1726 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_594441161 : Nat.Prime 594441161 := by
  apply lucas_primality 594441161 (3 : ZMod 594441161)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (14861029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (14861029, 1)] : List FactorBlock).map factorBlockValue).prod) = 594441161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_14861029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 594441161) ^ 297220580 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 594441161) ^ 118888232 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 594441161) ^ 40 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_624578257 : Nat.Prime 624578257 := by
  apply lucas_primality 624578257 (15 : ZMod 624578257)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (41, 1), (179, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (41, 1), (179, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 624578257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_179
      · exact prime_twentyFiveW_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 624578257) ^ 312289128 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 208192752 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 15233616 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 3489264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 3170448 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_710480009 : Nat.Prime 710480009 := by
  apply lucas_primality 710480009 (3 : ZMod 710480009)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (1812449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (1812449, 1)] : List FactorBlock).map factorBlockValue).prod) = 710480009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1812449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 710480009) ^ 355240004 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 710480009) ^ 101497144 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 710480009) ^ 392 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_722815057 : Nat.Prime 722815057 := by
  apply lucas_primality 722815057 (7 : ZMod 722815057)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (1673183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (1673183, 1)] : List FactorBlock).map factorBlockValue).prod) = 722815057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_1673183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 722815057) ^ 361407528 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 722815057) ^ 240938352 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 722815057) ^ 432 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_820267703 : Nat.Prime 820267703 := by
  apply lucas_primality 820267703 (5 : ZMod 820267703)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (410133851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (410133851, 1)] : List FactorBlock).map factorBlockValue).prod) = 820267703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_410133851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 820267703) ^ 410133851 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 820267703) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_847011563 : Nat.Prime 847011563 := by
  apply lucas_primality 847011563 (2 : ZMod 847011563)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (423505781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (423505781, 1)] : List FactorBlock).map factorBlockValue).prod) = 847011563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_423505781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 847011563) ^ 423505781 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 847011563) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1100273971 : Nat.Prime 1100273971 := by
  apply lucas_primality 1100273971 (3 : ZMod 1100273971)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (359, 1), (102161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (359, 1), (102161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100273971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_359
      · exact prime_twentyFiveW_102161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1100273971) ^ 550136985 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 366757990 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 220054794 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 3064830 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 10770 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_113
      · exact prime_twentyFiveW_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1246529923 : Nat.Prime 1246529923 := by
  apply lucas_primality 1246529923 (2 : ZMod 1246529923)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (569, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (569, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1246529923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_569
      · exact prime_twentyFiveW_1747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1246529923) ^ 623264961 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 415509974 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 113320902 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 65606838 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 2190738 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 713526 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1334422357 : Nat.Prime 1334422357 := by
  apply lucas_primality 1334422357 (5 : ZMod 1334422357)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (3834547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (3834547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334422357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_3834547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1334422357) ^ 667211178 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 444807452 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 46014564 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 348 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_409
      · exact prime_twentyFiveW_443
      · exact prime_twentyFiveW_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1931195141 : Nat.Prime 1931195141 := by
  apply lucas_primality 1931195141 (2 : ZMod 1931195141)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1447, 1), (9533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1447, 1), (9533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931195141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1447
      · exact prime_twentyFiveW_9533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1931195141) ^ 965597570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 386239028 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 275885020 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 1334620 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 202580 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_89
      · exact prime_twentyFiveW_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2013321539 : Nat.Prime 2013321539 := by
  apply lucas_primality 2013321539 (2 : ZMod 2013321539)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (12128443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (12128443, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013321539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_83
      · exact prime_twentyFiveW_12128443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2013321539) ^ 1006660769 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013321539) ^ 24256886 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013321539) ^ 166 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2049369011 : Nat.Prime 2049369011 := by
  apply lucas_primality 2049369011 (2 : ZMod 2049369011)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (384497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (384497, 1)] : List FactorBlock).map factorBlockValue).prod) = 2049369011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_384497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2049369011) ^ 1024684505 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 409873802 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 157643770 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 49984610 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 5330 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2050309799 : Nat.Prime 2050309799 := by
  apply lucas_primality 2050309799 (13 : ZMod 2050309799)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53955521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53955521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2050309799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_53955521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 2050309799) ^ 1025154899 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2050309799) ^ 107911042 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2050309799) ^ 38 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2057275783 : Nat.Prime 2057275783 := by
  apply lucas_primality 2057275783 (3 : ZMod 2057275783)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (114293099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (114293099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2057275783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_114293099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2057275783) ^ 1028637891 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2057275783) ^ 685758594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2057275783) ^ 18 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2072555033 : Nat.Prime 2072555033 := by
  apply lucas_primality 2072555033 (3 : ZMod 2072555033)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (4247039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (4247039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072555033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_4247039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2072555033) ^ 1036277516 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072555033) ^ 33976312 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072555033) ^ 488 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2101226821 : Nat.Prime 2101226821 := by
  apply lucas_primality 2101226821 (6 : ZMod 2101226821)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (43, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (43, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 2101226821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2101226821) ^ 1050613410 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 700408940 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 420245364 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 300175260 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 191020620 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 48865740 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2101226821) ^ 1390620 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2421149041 : Nat.Prime 2421149041 := by
  apply lucas_primality 2421149041 (17 : ZMod 2421149041)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (211, 1), (15937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (211, 1), (15937, 1)] : List FactorBlock).map factorBlockValue).prod) = 2421149041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_211
      · exact prime_twentyFiveW_15937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2421149041) ^ 1210574520 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2421149041) ^ 807049680 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2421149041) ^ 484229808 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2421149041) ^ 11474640 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2421149041) ^ 151920 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2860615019 : Nat.Prime 2860615019 := by
  apply lucas_primality 2860615019 (2 : ZMod 2860615019)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (1516763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (1516763, 1)] : List FactorBlock).map factorBlockValue).prod) = 2860615019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_1516763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2860615019) ^ 1430307509 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860615019) ^ 124374566 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860615019) ^ 69771098 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860615019) ^ 1886 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3684773879 : Nat.Prime 3684773879 := by
  apply lucas_primality 3684773879 (13 : ZMod 3684773879)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (3037, 1), (7309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (3037, 1), (7309, 1)] : List FactorBlock).map factorBlockValue).prod) = 3684773879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_83
      · exact prime_twentyFiveW_3037
      · exact prime_twentyFiveW_7309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3684773879) ^ 1842386939 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 3684773879) ^ 44394866 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 3684773879) ^ 1213294 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 3684773879) ^ 504142 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3862390283 : Nat.Prime 3862390283 := by
  apply lucas_primality 3862390283 (2 : ZMod 3862390283)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1931195141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1931195141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3862390283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_1931195141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3862390283) ^ 1931195141 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3862390283) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4070273261 : Nat.Prime 4070273261 := by
  apply lucas_primality 4070273261 (2 : ZMod 4070273261)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070273261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_97
      · exact prime_twentyFiveW_2098079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4070273261) ^ 2035136630 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 814054652 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 41961580 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 1940 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4260874759 : Nat.Prime 4260874759 := by
  apply lucas_primality 4260874759 (3 : ZMod 4260874759)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (733, 1), (138403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (733, 1), (138403, 1)] : List FactorBlock).map factorBlockValue).prod) = 4260874759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_733
      · exact prime_twentyFiveW_138403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4260874759) ^ 2130437379 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4260874759) ^ 1420291586 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4260874759) ^ 608696394 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4260874759) ^ 5812926 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4260874759) ^ 30786 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5503306021 : Nat.Prime 5503306021 := by
  apply lucas_primality 5503306021 (2 : ZMod 5503306021)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (91721767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (91721767, 1)] : List FactorBlock).map factorBlockValue).prod) = 5503306021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_91721767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5503306021) ^ 2751653010 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503306021) ^ 1834435340 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503306021) ^ 1100661204 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503306021) ^ 60 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5881403741 : Nat.Prime 5881403741 := by
  apply lucas_primality 5881403741 (2 : ZMod 5881403741)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (619, 1), (475073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (619, 1), (475073, 1)] : List FactorBlock).map factorBlockValue).prod) = 5881403741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_619
      · exact prime_twentyFiveW_475073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5881403741) ^ 2940701870 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5881403741) ^ 1176280748 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5881403741) ^ 9501460 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5881403741) ^ 12380 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_6057583319 : Nat.Prime 6057583319 := by
  apply lucas_primality 6057583319 (7 : ZMod 6057583319)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (557, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (557, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) = 6057583319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_167
      · exact prime_twentyFiveW_557
      · exact prime_twentyFiveW_32561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6057583319) ^ 3028791659 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 36272954 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 10875374 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 186038 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_6786591521 : Nat.Prime 6786591521 := by
  apply lucas_primality 6786591521 (3 : ZMod 6786591521)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (42416197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (42416197, 1)] : List FactorBlock).map factorBlockValue).prod) = 6786591521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_42416197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6786591521) ^ 3393295760 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6786591521) ^ 1357318304 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6786591521) ^ 160 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_6966777539 : Nat.Prime 6966777539 := by
  apply lucas_primality 6966777539 (2 : ZMod 6966777539)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (26190893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (26190893, 1)] : List FactorBlock).map factorBlockValue).prod) = 6966777539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_26190893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6966777539) ^ 3483388769 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6966777539) ^ 995253934 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6966777539) ^ 366672502 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6966777539) ^ 266 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_7389540247 : Nat.Prime 7389540247 := by
  apply lucas_primality 7389540247 (3 : ZMod 7389540247)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (31, 1), (212453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (31, 1), (212453, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389540247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_212453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7389540247) ^ 3694770123 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7389540247) ^ 2463180082 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7389540247) ^ 671776386 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7389540247) ^ 434678838 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7389540247) ^ 238372266 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7389540247) ^ 34782 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_9278485297 : Nat.Prime 9278485297 := by
  apply lucas_primality 9278485297 (5 : ZMod 9278485297)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9278485297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_193301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9278485297) ^ 4639242648 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 3092828432 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 48 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_10834859807 : Nat.Prime 10834859807 := by
  apply lucas_primality 10834859807 (5 : ZMod 10834859807)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30097, 1), (179999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30097, 1), (179999, 1)] : List FactorBlock).map factorBlockValue).prod) = 10834859807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_30097
      · exact prime_twentyFiveW_179999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10834859807) ^ 5417429903 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10834859807) ^ 359998 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10834859807) ^ 60194 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_15383
      · exact prime_twentyFiveW_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_12197644631 : Nat.Prime 12197644631 := by
  apply lucas_primality 12197644631 (7 : ZMod 12197644631)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (239, 1), (2039, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (239, 1), (2039, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) = 12197644631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_239
      · exact prime_twentyFiveW_2039
      · exact prime_twentyFiveW_2503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12197644631) ^ 6098822315 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 12197644631) ^ 2439528926 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 12197644631) ^ 51036170 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 12197644631) ^ 5982170 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 12197644631) ^ 4873210 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_13239683333 : Nat.Prime 13239683333 := by
  apply lucas_primality 13239683333 (2 : ZMod 13239683333)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (49009, 1), (67537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (49009, 1), (67537, 1)] : List FactorBlock).map factorBlockValue).prod) = 13239683333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_49009
      · exact prime_twentyFiveW_67537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13239683333) ^ 6619841666 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13239683333) ^ 270148 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13239683333) ^ 196036 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_13769726743 : Nat.Prime 13769726743 := by
  apply lucas_primality 13769726743 (3 : ZMod 13769726743)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5563, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5563, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13769726743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_5563
      · exact prime_twentyFiveW_8089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13769726743) ^ 6884863371 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 4589908914 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 809983926 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 2475234 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 1702278 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_349
      · exact prime_twentyFiveW_619
      · exact prime_twentyFiveW_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_17675938843 : Nat.Prime 17675938843 := by
  apply lucas_primality 17675938843 (3 : ZMod 17675938843)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (1373, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (1373, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) = 17675938843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_211
      · exact prime_twentyFiveW_1373
      · exact prime_twentyFiveW_10169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17675938843) ^ 8837969421 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17675938843) ^ 5891979614 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17675938843) ^ 83772222 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17675938843) ^ 12873954 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17675938843) ^ 1738218 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_17679196819 : Nat.Prime 17679196819 := by
  apply lucas_primality 17679196819 (3 : ZMod 17679196819)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (167, 1), (347, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (167, 1), (347, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 17679196819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_167
      · exact prime_twentyFiveW_347
      · exact prime_twentyFiveW_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17679196819) ^ 8839598409 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17679196819) ^ 5893065606 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17679196819) ^ 1039952754 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17679196819) ^ 105863454 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17679196819) ^ 50948694 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 17679196819) ^ 17732394 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_19170048893 : Nat.Prime 19170048893 := by
  apply lucas_primality 19170048893 (2 : ZMod 19170048893)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (15610789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (15610789, 1)] : List FactorBlock).map factorBlockValue).prod) = 19170048893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_307
      · exact prime_twentyFiveW_15610789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19170048893) ^ 9585024446 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 19170048893) ^ 62443156 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 19170048893) ^ 1228 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_19804931479 : Nat.Prime 19804931479 := by
  apply lucas_primality 19804931479 (3 : ZMod 19804931479)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1100273971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1100273971, 1)] : List FactorBlock).map factorBlockValue).prod) = 19804931479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_1100273971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19804931479) ^ 9902465739 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 19804931479) ^ 6601643826 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 19804931479) ^ 18 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_20238821597 : Nat.Prime 20238821597 := by
  apply lucas_primality 20238821597 (2 : ZMod 20238821597)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (722815057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (722815057, 1)] : List FactorBlock).map factorBlockValue).prod) = 20238821597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_722815057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20238821597) ^ 10119410798 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20238821597) ^ 2891260228 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20238821597) ^ 28 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_21796943101 : Nat.Prime 21796943101 := by
  apply lucas_primality 21796943101 (10 : ZMod 21796943101)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (181, 1), (401417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (181, 1), (401417, 1)] : List FactorBlock).map factorBlockValue).prod) = 21796943101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_181
      · exact prime_twentyFiveW_401417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21796943101) ^ 10898471550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 7265647700 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 4359388620 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 120425100 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 54300 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_23005888109 : Nat.Prime 23005888109 := by
  apply lucas_primality 23005888109 (2 : ZMod 23005888109)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1823, 1), (450707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1823, 1), (450707, 1)] : List FactorBlock).map factorBlockValue).prod) = 23005888109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1823
      · exact prime_twentyFiveW_450707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23005888109) ^ 11502944054 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005888109) ^ 3286555444 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005888109) ^ 12619796 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005888109) ^ 51044 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_24395289263 : Nat.Prime 24395289263 := by
  apply lucas_primality 24395289263 (5 : ZMod 24395289263)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12197644631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12197644631, 1)] : List FactorBlock).map factorBlockValue).prod) = 24395289263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_12197644631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 24395289263) ^ 12197644631 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 24395289263) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_26391775451 : Nat.Prime 26391775451 := by
  apply lucas_primality 26391775451 (2 : ZMod 26391775451)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17489, 1), (30181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17489, 1), (30181, 1)] : List FactorBlock).map factorBlockValue).prod) = 26391775451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_17489
      · exact prime_twentyFiveW_30181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26391775451) ^ 13195887725 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 26391775451) ^ 5278355090 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 26391775451) ^ 1509050 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 26391775451) ^ 874450 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_71
      · exact prime_twentyFiveW_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_30890258779 : Nat.Prime 30890258779 := by
  apply lucas_primality 30890258779 (3 : ZMod 30890258779)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2111, 1), (2438833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2111, 1), (2438833, 1)] : List FactorBlock).map factorBlockValue).prod) = 30890258779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_2111
      · exact prime_twentyFiveW_2438833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30890258779) ^ 15445129389 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 10296752926 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 14632998 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 12666 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_40632070151 : Nat.Prime 40632070151 := by
  apply lucas_primality 40632070151 (14 : ZMod 40632070151)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1433, 1), (81013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1433, 1), (81013, 1)] : List FactorBlock).map factorBlockValue).prod) = 40632070151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1433
      · exact prime_twentyFiveW_81013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 40632070151) ^ 20316035075 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 40632070151) ^ 8126414030 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 40632070151) ^ 5804581450 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 40632070151) ^ 28354550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 40632070151) ^ 501550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_54743994013 : Nat.Prime 54743994013 := by
  apply lucas_primality 54743994013 (2 : ZMod 54743994013)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (163, 1), (233, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (163, 1), (233, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 54743994013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_113
      · exact prime_twentyFiveW_163
      · exact prime_twentyFiveW_233
      · exact prime_twentyFiveW_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54743994013) ^ 27371997006 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 18247998004 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 484460124 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 335852724 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 234952764 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 51499524 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_56463796133 : Nat.Prime 56463796133 := by
  apply lucas_primality 56463796133 (2 : ZMod 56463796133)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (266338661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (266338661, 1)] : List FactorBlock).map factorBlockValue).prod) = 56463796133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_266338661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56463796133) ^ 28231898066 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56463796133) ^ 1065354644 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56463796133) ^ 212 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_58596351661 : Nat.Prime 58596351661 := by
  apply lucas_primality 58596351661 (2 : ZMod 58596351661)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (37, 1), (163, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (37, 1), (163, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) = 58596351661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_163
      · exact prime_twentyFiveW_701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58596351661) ^ 29298175830 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 19532117220 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 11719270332 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 8370907380 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 5326941060 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 1583685180 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 359486820 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 83589660 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_81709378843 : Nat.Prime 81709378843 := by
  apply lucas_primality 81709378843 (5 : ZMod 81709378843)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (149650877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (149650877, 1)] : List FactorBlock).map factorBlockValue).prod) = 81709378843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_149650877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 81709378843) ^ 40854689421 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 27236459614 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 11672768406 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 6285336834 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 546 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_101716938553 : Nat.Prime 101716938553 := by
  apply lucas_primality 101716938553 (5 : ZMod 101716938553)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (127, 1), (33371699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (127, 1), (33371699, 1)] : List FactorBlock).map factorBlockValue).prod) = 101716938553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_127
      · exact prime_twentyFiveW_33371699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 101716938553) ^ 50858469276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 101716938553) ^ 33905646184 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 101716938553) ^ 800920776 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 101716938553) ^ 3048 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_103335410687 : Nat.Prime 103335410687 := by
  apply lucas_primality 103335410687 (5 : ZMod 103335410687)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (847011563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (847011563, 1)] : List FactorBlock).map factorBlockValue).prod) = 103335410687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_847011563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 103335410687) ^ 51667705343 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 103335410687) ^ 1694023126 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 103335410687) ^ 122 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_122671363769 : Nat.Prime 122671363769 := by
  apply lucas_primality 122671363769 (3 : ZMod 122671363769)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (414430283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (414430283, 1)] : List FactorBlock).map factorBlockValue).prod) = 122671363769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_414430283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 122671363769) ^ 61335681884 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 122671363769) ^ 3315442264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 122671363769) ^ 296 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_177829524883 : Nat.Prime 177829524883 := by
  apply lucas_primality 177829524883 (2 : ZMod 177829524883)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 2), (5039, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 2), (5039, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) = 177829524883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_5039
      · exact prime_twentyFiveW_5431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 177829524883) ^ 88914762441 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 59276508294 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 9359448678 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 35290638 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 32743422 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_230040586717 : Nat.Prime 230040586717 := by
  apply lucas_primality 230040586717 (5 : ZMod 230040586717)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19170048893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19170048893, 1)] : List FactorBlock).map factorBlockValue).prod) = 230040586717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_19170048893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 230040586717) ^ 115020293358 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 230040586717) ^ 76680195572 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 230040586717) ^ 12 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_338782776799 : Nat.Prime 338782776799 := by
  apply lucas_primality 338782776799 (3 : ZMod 338782776799)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (56463796133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (56463796133, 1)] : List FactorBlock).map factorBlockValue).prod) = 338782776799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_56463796133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 338782776799) ^ 169391388399 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 338782776799) ^ 112927592266 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 338782776799) ^ 6 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_364298788747 : Nat.Prime 364298788747 := by
  apply lucas_primality 364298788747 (2 : ZMod 364298788747)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (20238821597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (20238821597, 1)] : List FactorBlock).map factorBlockValue).prod) = 364298788747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_20238821597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 364298788747) ^ 182149394373 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 364298788747) ^ 121432929582 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 364298788747) ^ 18 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_417738454307 : Nat.Prime 417738454307 := by
  apply lucas_primality 417738454307 (2 : ZMod 417738454307)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3359, 1), (62181967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3359, 1), (62181967, 1)] : List FactorBlock).map factorBlockValue).prod) = 417738454307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3359
      · exact prime_twentyFiveW_62181967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 417738454307) ^ 208869227153 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 417738454307) ^ 124363934 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 417738454307) ^ 6718 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_428348173229 : Nat.Prime 428348173229 := by
  apply lucas_primality 428348173229 (2 : ZMod 428348173229)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4999, 1), (21421693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4999, 1), (21421693, 1)] : List FactorBlock).map factorBlockValue).prod) = 428348173229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_4999
      · exact prime_twentyFiveW_21421693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 428348173229) ^ 214174086614 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 428348173229) ^ 85686772 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 428348173229) ^ 19996 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_397
      · exact prime_twentyFiveW_2531
      · exact prime_twentyFiveW_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_482114616773 : Nat.Prime 482114616773 := by
  apply lucas_primality 482114616773 (2 : ZMod 482114616773)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (41, 1), (79, 1), (1200377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (41, 1), (79, 1), (1200377, 1)] : List FactorBlock).map factorBlockValue).prod) = 482114616773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_1200377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 482114616773) ^ 241057308386 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 482114616773) ^ 15552084412 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 482114616773) ^ 11758893092 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 482114616773) ^ 6102716668 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 482114616773) ^ 401636 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_506923540391 : Nat.Prime 506923540391 := by
  apply lucas_primality 506923540391 (7 : ZMod 506923540391)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (41, 1), (113, 1), (475721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (41, 1), (113, 1), (475721, 1)] : List FactorBlock).map factorBlockValue).prod) = 506923540391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_113
      · exact prime_twentyFiveW_475721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 506923540391) ^ 253461770195 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 506923540391) ^ 101384708078 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 506923540391) ^ 22040153930 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 506923540391) ^ 12363988790 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 506923540391) ^ 4486049030 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 506923540391) ^ 1065590 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_570399980551 : Nat.Prime 570399980551 := by
  apply lucas_primality 570399980551 (3 : ZMod 570399980551)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (19841, 1), (191657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (19841, 1), (191657, 1)] : List FactorBlock).map factorBlockValue).prod) = 570399980551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_19841
      · exact prime_twentyFiveW_191657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 570399980551) ^ 285199990275 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 570399980551) ^ 190133326850 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 570399980551) ^ 114079996110 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 570399980551) ^ 28748550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 570399980551) ^ 2976150 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_620395625561 : Nat.Prime 620395625561 := by
  apply lucas_primality 620395625561 (3 : ZMod 620395625561)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (757, 1), (20488627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (757, 1), (20488627, 1)] : List FactorBlock).map factorBlockValue).prod) = 620395625561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_757
      · exact prime_twentyFiveW_20488627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 620395625561) ^ 310197812780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 620395625561) ^ 124079125112 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 620395625561) ^ 819545080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 620395625561) ^ 30280 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_650051402041 : Nat.Prime 650051402041 := by
  apply lucas_primality 650051402041 (11 : ZMod 650051402041)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (79, 1), (199, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (79, 1), (199, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod) = 650051402041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_199
      · exact prime_twentyFiveW_114859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 650051402041) ^ 325025701020 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 216683800680 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 130010280408 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 8228498760 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 3266589960 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 5659560 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_702509983793 : Nat.Prime 702509983793 := by
  apply lucas_primality 702509983793 (3 : ZMod 702509983793)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (16567, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (16567, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) = 702509983793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_131
      · exact prime_twentyFiveW_16567
      · exact prime_twentyFiveW_20231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 702509983793) ^ 351254991896 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 5362671632 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 42404176 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 34724432 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1024602149047 : Nat.Prime 1024602149047 := by
  apply lucas_primality 1024602149047 (17 : ZMod 1024602149047)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (24395289263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (24395289263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024602149047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_24395289263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1024602149047) ^ 512301074523 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 1024602149047) ^ 341534049682 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 1024602149047) ^ 146371735578 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 1024602149047) ^ 42 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1065742907407 : Nat.Prime 1065742907407 := by
  apply lucas_primality 1065742907407 (5 : ZMod 1065742907407)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36997, 1), (4801033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36997, 1), (4801033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065742907407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_36997
      · exact prime_twentyFiveW_4801033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1065742907407) ^ 532871453703 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 355247635802 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 28806198 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 221982 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1066883369399 : Nat.Prime 1066883369399 := by
  apply lucas_primality 1066883369399 (11 : ZMod 1066883369399)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (131, 1), (3967, 1), (13331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (131, 1), (3967, 1), (13331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1066883369399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_131
      · exact prime_twentyFiveW_3967
      · exact prime_twentyFiveW_13331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1066883369399) ^ 533441684699 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 152411909914 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 96989397218 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 8144147858 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 268939594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 80030258 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1088118763427 : Nat.Prime 1088118763427 := by
  apply lucas_primality 1088118763427 (2 : ZMod 1088118763427)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (4201, 1), (857663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (4201, 1), (857663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088118763427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_151
      · exact prime_twentyFiveW_4201
      · exact prime_twentyFiveW_857663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1088118763427) ^ 544059381713 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088118763427) ^ 7206084526 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088118763427) ^ 259014226 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088118763427) ^ 1268702 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1130831493331 : Nat.Prime 1130831493331 := by
  apply lucas_primality 1130831493331 (2 : ZMod 1130831493331)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (67, 1), (569, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (67, 1), (569, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130831493331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_67
      · exact prime_twentyFiveW_569
      · exact prime_twentyFiveW_12841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130831493331) ^ 565415746665 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 376943831110 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 226166298666 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 161547356190 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 102802863030 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 16878081990 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 1987401570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 88064130 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1185399396581 : Nat.Prime 1185399396581 := by
  apply lucas_primality 1185399396581 (2 : ZMod 1185399396581)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (137, 1), (389, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (137, 1), (389, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185399396581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_137
      · exact prime_twentyFiveW_389
      · exact prime_twentyFiveW_22697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1185399396581) ^ 592699698290 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 237079879316 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 169342770940 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 8652550340 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 3047299220 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 52227140 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1191571499971 : Nat.Prime 1191571499971 := by
  apply lucas_primality 1191571499971 (3 : ZMod 1191571499971)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13239683333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13239683333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1191571499971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_13239683333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1191571499971) ^ 595785749985 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1191571499971) ^ 397190499990 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1191571499971) ^ 238314299994 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1191571499971) ^ 90 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1372447766351 : Nat.Prime 1372447766351 := by
  apply lucas_primality 1372447766351 (7 : ZMod 1372447766351)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1372447766351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_9473
      · exact prime_twentyFiveW_170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1372447766351) ^ 686223883175 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 274489553270 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 80732221550 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 144879950 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 8052050 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1405019967587 : Nat.Prime 1405019967587 := by
  apply lucas_primality 1405019967587 (2 : ZMod 1405019967587)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (702509983793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (702509983793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405019967587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_702509983793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1405019967587) ^ 702509983793 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1405019967587) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_397
      · exact prime_twentyFiveW_977
      · exact prime_twentyFiveW_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1447535876737 : Nat.Prime 1447535876737 := by
  apply lucas_primality 1447535876737 (7 : ZMod 1447535876737)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (9137, 1), (412567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (9137, 1), (412567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1447535876737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_9137
      · exact prime_twentyFiveW_412567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1447535876737) ^ 723767938368 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 482511958912 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 158425728 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 3508608 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_35279
      · exact prime_twentyFiveW_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1726920139561 : Nat.Prime 1726920139561 := by
  apply lucas_primality 1726920139561 (23 : ZMod 1726920139561)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (12809, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (12809, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1726920139561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_12809
      · exact prime_twentyFiveW_14591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1726920139561) ^ 863460069780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 575640046520 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 345384027912 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 246702877080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 156992739960 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 134820840 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 118355160 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1742833970153 : Nat.Prime 1742833970153 := by
  apply lucas_primality 1742833970153 (3 : ZMod 1742833970153)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19804931479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19804931479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1742833970153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_19804931479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1742833970153) ^ 871416985076 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1742833970153) ^ 158439451832 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1742833970153) ^ 88 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2091461964649 : Nat.Prime 2091461964649 := by
  apply lucas_primality 2091461964649 (13 : ZMod 2091461964649)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (78041, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (78041, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091461964649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_78041
      · exact prime_twentyFiveW_159521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2091461964649) ^ 1045730982324 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 697153988216 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 298780280664 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 26799528 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 13110888 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2220746035367 : Nat.Prime 2220746035367 := by
  apply lucas_primality 2220746035367 (5 : ZMod 2220746035367)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (113, 1), (317, 1), (837779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (113, 1), (317, 1), (837779, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220746035367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_113
      · exact prime_twentyFiveW_317
      · exact prime_twentyFiveW_837779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2220746035367) ^ 1110373017683 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2220746035367) ^ 60020163118 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2220746035367) ^ 19652619782 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2220746035367) ^ 7005507998 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2220746035367) ^ 2650754 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2625207939961 : Nat.Prime 2625207939961 := by
  apply lucas_primality 2625207939961 (14 : ZMod 2625207939961)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (239, 1), (1303, 1), (70249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (239, 1), (1303, 1), (70249, 1)] : List FactorBlock).map factorBlockValue).prod) = 2625207939961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_239
      · exact prime_twentyFiveW_1303
      · exact prime_twentyFiveW_70249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2625207939961) ^ 1312603969980 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 875069313320 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 525041587992 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 10984133640 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 2014741320 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 37370040 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2659378548317 : Nat.Prime 2659378548317 := by
  apply lucas_primality 2659378548317 (2 : ZMod 2659378548317)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (10667, 1), (8903891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (10667, 1), (8903891, 1)] : List FactorBlock).map factorBlockValue).prod) = 2659378548317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_10667
      · exact prime_twentyFiveW_8903891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2659378548317) ^ 1329689274158 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 379911221188 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 249308948 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 298676 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2697704043659 : Nat.Prime 2697704043659 := by
  apply lucas_primality 2697704043659 (2 : ZMod 2697704043659)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41203, 1), (2518211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41203, 1), (2518211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2697704043659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_41203
      · exact prime_twentyFiveW_2518211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2697704043659) ^ 1348852021829 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2697704043659) ^ 207515695666 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2697704043659) ^ 65473486 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2697704043659) ^ 1071278 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2716373653627 : Nat.Prime 2716373653627 := by
  apply lucas_primality 2716373653627 (3 : ZMod 2716373653627)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39103, 1), (11577857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39103, 1), (11577857, 1)] : List FactorBlock).map factorBlockValue).prod) = 2716373653627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_39103
      · exact prime_twentyFiveW_11577857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2716373653627) ^ 1358186826813 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2716373653627) ^ 905457884542 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2716373653627) ^ 69467142 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2716373653627) ^ 234618 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_761
      · exact prime_twentyFiveW_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3628626968867 : Nat.Prime 3628626968867 := by
  apply lucas_primality 3628626968867 (2 : ZMod 3628626968867)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4357, 1), (416413469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4357, 1), (416413469, 1)] : List FactorBlock).map factorBlockValue).prod) = 3628626968867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_4357
      · exact prime_twentyFiveW_416413469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3628626968867) ^ 1814313484433 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3628626968867) ^ 832826938 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3628626968867) ^ 8714 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4012963349977 : Nat.Prime 4012963349977 := by
  apply lucas_primality 4012963349977 (5 : ZMod 4012963349977)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (521, 1), (2183227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (521, 1), (2183227, 1)] : List FactorBlock).map factorBlockValue).prod) = 4012963349977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_521
      · exact prime_twentyFiveW_2183227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4012963349977) ^ 2006481674988 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4012963349977) ^ 1337654449992 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4012963349977) ^ 573280478568 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4012963349977) ^ 7702424856 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4012963349977) ^ 1838088 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_381559
      · exact prime_twentyFiveW_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5597206986757 : Nat.Prime 5597206986757 := by
  apply lucas_primality 5597206986757 (2 : ZMod 5597206986757)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (6057583319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (6057583319, 1)] : List FactorBlock).map factorBlockValue).prod) = 5597206986757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_6057583319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5597206986757) ^ 2798603493378 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 1865735662252 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 799600998108 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 508836998796 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 924 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_6279845155949 : Nat.Prime 6279845155949 := by
  apply lucas_primality 6279845155949 (2 : ZMod 6279845155949)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (89, 1), (2053, 1), (94421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (89, 1), (2053, 1), (94421, 1)] : List FactorBlock).map factorBlockValue).prod) = 6279845155949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_89
      · exact prime_twentyFiveW_2053
      · exact prime_twentyFiveW_94421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6279845155949) ^ 3139922577974 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 897120736564 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 483065011996 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 70560057932 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 3058862716 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 66508988 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_8704950107417 : Nat.Prime 8704950107417 := by
  apply lucas_primality 8704950107417 (3 : ZMod 8704950107417)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1088118763427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1088118763427, 1)] : List FactorBlock).map factorBlockValue).prod) = 8704950107417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_1088118763427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 8704950107417) ^ 4352475053708 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8704950107417) ^ 8 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_9825009110321 : Nat.Prime 9825009110321 := by
  apply lucas_primality 9825009110321 (3 : ZMod 9825009110321)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (61, 1), (2013321539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (61, 1), (2013321539, 1)] : List FactorBlock).map factorBlockValue).prod) = 9825009110321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_2013321539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9825009110321) ^ 4912504555160 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 1965001822064 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 161065723120 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 4880 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_11074551087949 : Nat.Prime 11074551087949 := by
  apply lucas_primality 11074551087949 (2 : ZMod 11074551087949)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (19, 1), (71, 1), (1151, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (19, 1), (71, 1), (1151, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) = 11074551087949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_71
      · exact prime_twentyFiveW_1151
      · exact prime_twentyFiveW_34963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11074551087949) ^ 5537275543974 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 3691517029316 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 651444181644 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 582871109892 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 155979592788 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 9621677748 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 316750596 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_19649401054343 : Nat.Prime 19649401054343 := by
  apply lucas_primality 19649401054343 (5 : ZMod 19649401054343)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (338782776799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (338782776799, 1)] : List FactorBlock).map factorBlockValue).prod) = 19649401054343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_338782776799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19649401054343) ^ 9824700527171 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 19649401054343) ^ 677565553598 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 19649401054343) ^ 58 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_24581705669203 : Nat.Prime 24581705669203 := by
  apply lucas_primality 24581705669203 (2 : ZMod 24581705669203)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1609, 1), (231479233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1609, 1), (231479233, 1)] : List FactorBlock).map factorBlockValue).prod) = 24581705669203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_1609
      · exact prime_twentyFiveW_231479233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24581705669203) ^ 12290852834601 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581705669203) ^ 8193901889734 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581705669203) ^ 2234700515382 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581705669203) ^ 15277629378 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581705669203) ^ 106194 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_26932669760303 : Nat.Prime 26932669760303 := by
  apply lucas_primality 26932669760303 (5 : ZMod 26932669760303)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16417, 1), (820267703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16417, 1), (820267703, 1)] : List FactorBlock).map factorBlockValue).prod) = 26932669760303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_16417
      · exact prime_twentyFiveW_820267703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26932669760303) ^ 13466334880151 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 26932669760303) ^ 1640535406 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 26932669760303) ^ 32834 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_31084562512099 : Nat.Prime 31084562512099 := by
  apply lucas_primality 31084562512099 (2 : ZMod 31084562512099)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1726920139561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1726920139561, 1)] : List FactorBlock).map factorBlockValue).prod) = 31084562512099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_1726920139561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31084562512099) ^ 15542281256049 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31084562512099) ^ 10361520837366 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31084562512099) ^ 18 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_33084042641141 : Nat.Prime 33084042641141 := by
  apply lucas_primality 33084042641141 (2 : ZMod 33084042641141)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (139, 1), (151, 1), (78812813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (139, 1), (151, 1), (78812813, 1)] : List FactorBlock).map factorBlockValue).prod) = 33084042641141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_139
      · exact prime_twentyFiveW_151
      · exact prime_twentyFiveW_78812813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33084042641141) ^ 16542021320570 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33084042641141) ^ 6616808528228 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33084042641141) ^ 238014695260 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33084042641141) ^ 219099620140 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33084042641141) ^ 419780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_37734539424529 : Nat.Prime 37734539424529 := by
  apply lucas_primality 37734539424529 (11 : ZMod 37734539424529)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (124739, 1), (6302249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (124739, 1), (6302249, 1)] : List FactorBlock).map factorBlockValue).prod) = 37734539424529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_124739
      · exact prime_twentyFiveW_6302249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 37734539424529) ^ 18867269712264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 37734539424529) ^ 12578179808176 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 37734539424529) ^ 302507952 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 37734539424529) ^ 5987472 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_41806160925181 : Nat.Prime 41806160925181 := by
  apply lucas_primality 41806160925181 (10 : ZMod 41806160925181)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (181, 1), (8809049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (181, 1), (8809049, 1)] : List FactorBlock).map factorBlockValue).prod) = 41806160925181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_181
      · exact prime_twentyFiveW_8809049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 41806160925181) ^ 20903080462590 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 13935386975060 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 8361232185036 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 2200324259220 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 1817659170660 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 230973264780 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 41806160925181) ^ 4745820 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_54446974002341 : Nat.Prime 54446974002341 := by
  apply lucas_primality 54446974002341 (3 : ZMod 54446974002341)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (67, 1), (40632070151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (67, 1), (40632070151, 1)] : List FactorBlock).map factorBlockValue).prod) = 54446974002341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_67
      · exact prime_twentyFiveW_40632070151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54446974002341) ^ 27223487001170 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 54446974002341) ^ 10889394800468 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 54446974002341) ^ 812641403020 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 54446974002341) ^ 1340 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_70951236721691 : Nat.Prime 70951236721691 := by
  apply lucas_primality 70951236721691 (2 : ZMod 70951236721691)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (409, 1), (1334422357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (409, 1), (1334422357, 1)] : List FactorBlock).map factorBlockValue).prod) = 70951236721691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_409
      · exact prime_twentyFiveW_1334422357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70951236721691) ^ 35475618360845 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 14190247344338 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 5457787440130 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 173474906410 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 53170 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_72876870840589 : Nat.Prime 72876870840589 := by
  apply lucas_primality 72876870840589 (10 : ZMod 72876870840589)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71711, 1), (84688159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71711, 1), (84688159, 1)] : List FactorBlock).map factorBlockValue).prod) = 72876870840589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_71711
      · exact prime_twentyFiveW_84688159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 72876870840589) ^ 36438435420294 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 72876870840589) ^ 24292290280196 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 72876870840589) ^ 1016257908 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 72876870840589) ^ 860532 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_101408018718397 : Nat.Prime 101408018718397 := by
  apply lucas_primality 101408018718397 (2 : ZMod 101408018718397)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (650051402041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (650051402041, 1)] : List FactorBlock).map factorBlockValue).prod) = 101408018718397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_650051402041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101408018718397) ^ 50704009359198 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 33802672906132 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 7800616824492 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 156 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_120840916763657 : Nat.Prime 120840916763657 := by
  apply lucas_primality 120840916763657 (3 : ZMod 120840916763657)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (89, 1), (97, 1), (5939, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (89, 1), (97, 1), (5939, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) = 120840916763657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_89
      · exact prime_twentyFiveW_97
      · exact prime_twentyFiveW_5939
      · exact prime_twentyFiveW_10159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 120840916763657) ^ 60420458381828 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 120840916763657) ^ 4166928164264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 120840916763657) ^ 1357763109704 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 120840916763657) ^ 1245782647048 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 120840916763657) ^ 20347014104 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 120840916763657) ^ 11894961784 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_1163
      · exact prime_twentyFiveW_1663
      · exact prime_twentyFiveW_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_290907674250203 : Nat.Prime 290907674250203 := by
  apply lucas_primality 290907674250203 (2 : ZMod 290907674250203)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (116687, 1), (1246529923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (116687, 1), (1246529923, 1)] : List FactorBlock).map factorBlockValue).prod) = 290907674250203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_116687
      · exact prime_twentyFiveW_1246529923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290907674250203) ^ 145453837125101 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 290907674250203) ^ 2493059846 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 290907674250203) ^ 233374 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_394714381038589 : Nat.Prime 394714381038589 := by
  apply lucas_primality 394714381038589 (6 : ZMod 394714381038589)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (21401, 1), (39409691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (21401, 1), (39409691, 1)] : List FactorBlock).map factorBlockValue).prod) = 394714381038589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_21401
      · exact prime_twentyFiveW_39409691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 394714381038589) ^ 197357190519294 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 394714381038589) ^ 131571460346196 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 394714381038589) ^ 30362644695276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 394714381038589) ^ 18443735388 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 394714381038589) ^ 10015668 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_537331870728673 : Nat.Prime 537331870728673 := by
  apply lucas_primality 537331870728673 (7 : ZMod 537331870728673)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5597206986757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5597206986757, 1)] : List FactorBlock).map factorBlockValue).prod) = 537331870728673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5597206986757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 537331870728673) ^ 268665935364336 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 537331870728673) ^ 179110623576224 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 537331870728673) ^ 96 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_596394404692817 : Nat.Prime 596394404692817 := by
  apply lucas_primality 596394404692817 (3 : ZMod 596394404692817)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2707, 1), (13769726743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2707, 1), (13769726743, 1)] : List FactorBlock).map factorBlockValue).prod) = 596394404692817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_2707
      · exact prime_twentyFiveW_13769726743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 596394404692817) ^ 298197202346408 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 596394404692817) ^ 220315627888 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 596394404692817) ^ 43312 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_808557301816729 : Nat.Prime 808557301816729 := by
  apply lucas_primality 808557301816729 (14 : ZMod 808557301816729)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (223, 1), (3684773879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (223, 1), (3684773879, 1)] : List FactorBlock).map factorBlockValue).prod) = 808557301816729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_223
      · exact prime_twentyFiveW_3684773879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 808557301816729) ^ 404278650908364 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 808557301816729) ^ 269519100605576 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 808557301816729) ^ 19720909800408 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 808557301816729) ^ 3625817496936 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 808557301816729) ^ 219432 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_857580112926659 : Nat.Prime 857580112926659 := by
  apply lucas_primality 857580112926659 (2 : ZMod 857580112926659)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17209, 1), (46219, 1), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17209, 1), (46219, 1), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) = 857580112926659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_17209
      · exact prime_twentyFiveW_46219
      · exact prime_twentyFiveW_49009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 857580112926659) ^ 428790056463329 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 77961828447878 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 49833233362 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 18554709382 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 17498420962 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1008315646774549 : Nat.Prime 1008315646774549 := by
  apply lucas_primality 1008315646774549 (10 : ZMod 1008315646774549)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1723, 1), (6966777539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1723, 1), (6966777539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008315646774549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_1723
      · exact prime_twentyFiveW_6966777539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1008315646774549) ^ 504157823387274 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1008315646774549) ^ 336105215591516 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1008315646774549) ^ 144045092396364 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1008315646774549) ^ 585209313276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1008315646774549) ^ 144732 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_71
      · exact prime_twentyFiveW_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1152234038950921 : Nat.Prime 1152234038950921 := by
  apply lucas_primality 1152234038950921 (14 : ZMod 1152234038950921)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (1066883369399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (1066883369399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152234038950921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_1066883369399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1152234038950921) ^ 576117019475460 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 384078012983640 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 230446807790184 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 1080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1472991480313183 : Nat.Prime 1472991480313183 := by
  apply lucas_primality 1472991480313183 (5 : ZMod 1472991480313183)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472991480313183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_156521
      · exact prime_twentyFiveW_522823519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1472991480313183) ^ 736495740156591 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 490997160104394 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 9410823342 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 2817378 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2797446213614389 : Nat.Prime 2797446213614389 := by
  apply lucas_primality 2797446213614389 (2 : ZMod 2797446213614389)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (589507, 1), (56492851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (589507, 1), (56492851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2797446213614389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_589507
      · exact prime_twentyFiveW_56492851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2797446213614389) ^ 1398723106807194 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 932482071204796 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 399635173373484 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 4745399484 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 49518588 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3141863835855083 : Nat.Prime 3141863835855083 := by
  apply lucas_primality 3141863835855083 (5 : ZMod 3141863835855083)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (120840916763657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (120840916763657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3141863835855083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_120840916763657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3141863835855083) ^ 1570931917927541 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3141863835855083) ^ 241681833527314 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3141863835855083) ^ 26 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3593722313513149 : Nat.Prime 3593722313513149 := by
  apply lucas_primality 3593722313513149 (6 : ZMod 3593722313513149)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (512713, 1), (5358737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (512713, 1), (5358737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3593722313513149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_109
      · exact prime_twentyFiveW_512713
      · exact prime_twentyFiveW_5358737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3593722313513149) ^ 1796861156756574 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 1197907437837716 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 32969929481772 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 7009227996 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 670628604 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3837748946372357 : Nat.Prime 3837748946372357 := by
  apply lucas_primality 3837748946372357 (2 : ZMod 3837748946372357)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (33084042641141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (33084042641141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3837748946372357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_33084042641141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3837748946372357) ^ 1918874473186178 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3837748946372357) ^ 132336170564564 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3837748946372357) ^ 116 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_7433440825740079 : Nat.Prime 7433440825740079 := by
  apply lucas_primality 7433440825740079 (3 : ZMod 7433440825740079)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (72876870840589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (72876870840589, 1)] : List FactorBlock).map factorBlockValue).prod) = 7433440825740079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_72876870840589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7433440825740079) ^ 3716720412870039 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7433440825740079) ^ 2477813608580026 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7433440825740079) ^ 437261225043534 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7433440825740079) ^ 102 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_67
      · exact prime_twentyFiveW_97
      · exact prime_twentyFiveW_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_12866222659007413 : Nat.Prime 12866222659007413 := by
  apply lucas_primality 12866222659007413 (2 : ZMod 12866222659007413)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (67, 1), (242819, 1), (1292237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (67, 1), (242819, 1), (1292237, 1)] : List FactorBlock).map factorBlockValue).prod) = 12866222659007413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_67
      · exact prime_twentyFiveW_242819
      · exact prime_twentyFiveW_1292237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12866222659007413) ^ 6433111329503706 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 4288740886335804 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 756836627000436 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 192033174015036 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 52986885948 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 9956550276 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_13420288955312027 : Nat.Prime 13420288955312027 := by
  apply lucas_primality 13420288955312027 (2 : ZMod 13420288955312027)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (394714381038589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (394714381038589, 1)] : List FactorBlock).map factorBlockValue).prod) = 13420288955312027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_394714381038589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13420288955312027) ^ 6710144477656013 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13420288955312027) ^ 789428762077178 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13420288955312027) ^ 34 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_15015461856106597 : Nat.Prime 15015461856106597 := by
  apply lucas_primality 15015461856106597 (5 : ZMod 15015461856106597)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12109, 1), (103335410687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12109, 1), (103335410687, 1)] : List FactorBlock).map factorBlockValue).prod) = 15015461856106597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_12109
      · exact prime_twentyFiveW_103335410687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15015461856106597) ^ 7507730928053298 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15015461856106597) ^ 5005153952035532 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15015461856106597) ^ 1240024928244 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15015461856106597) ^ 145308 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_16704183438336529 : Nat.Prime 16704183438336529 := by
  apply lucas_primality 16704183438336529 (19 : ZMod 16704183438336529)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (43, 1), (2697704043659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (43, 1), (2697704043659, 1)] : List FactorBlock).map factorBlockValue).prod) = 16704183438336529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_2697704043659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 16704183438336529) ^ 8352091719168264 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 16704183438336529) ^ 5568061146112176 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 16704183438336529) ^ 388469382286896 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 16704183438336529) ^ 6192 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_21712985397389927 : Nat.Prime 21712985397389927 := by
  apply lucas_primality 21712985397389927 (5 : ZMod 21712985397389927)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (4133, 1), (14783, 1), (169067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (4133, 1), (14783, 1), (169067, 1)] : List FactorBlock).map factorBlockValue).prod) = 21712985397389927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_1051
      · exact prime_twentyFiveW_4133
      · exact prime_twentyFiveW_14783
      · exact prime_twentyFiveW_169067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21712985397389927) ^ 10856492698694963 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21712985397389927) ^ 20659358132626 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21712985397389927) ^ 5253565303022 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21712985397389927) ^ 1468780720922 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 21712985397389927) ^ 128428288178 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_22540789770483337 : Nat.Prime 22540789770483337 := by
  apply lucas_primality 22540789770483337 (5 : ZMod 22540789770483337)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (8590367, 1), (9939247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (8590367, 1), (9939247, 1)] : List FactorBlock).map factorBlockValue).prod) = 22540789770483337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_8590367
      · exact prime_twentyFiveW_9939247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22540789770483337) ^ 11270394885241668 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 7513596590161112 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2049162706407576 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2623961208 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2267856888 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_24270372050913383 : Nat.Prime 24270372050913383 := by
  apply lucas_primality 24270372050913383 (5 : ZMod 24270372050913383)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (4111, 1), (17675938843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (4111, 1), (17675938843, 1)] : List FactorBlock).map factorBlockValue).prod) = 24270372050913383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_167
      · exact prime_twentyFiveW_4111
      · exact prime_twentyFiveW_17675938843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24270372050913383) ^ 12135186025456691 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 24270372050913383) ^ 145331569167146 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 24270372050913383) ^ 5903763573562 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 24270372050913383) ^ 1373074 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_656951
      · exact prime_twentyFiveW_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_30354743159973073 : Nat.Prime 30354743159973073 := by
  apply lucas_primality 30354743159973073 (5 : ZMod 30354743159973073)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (37, 1), (163, 1), (4157, 1), (8408039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (37, 1), (163, 1), (4157, 1), (8408039, 1)] : List FactorBlock).map factorBlockValue).prod) = 30354743159973073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_163
      · exact prime_twentyFiveW_4157
      · exact prime_twentyFiveW_8408039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30354743159973073) ^ 15177371579986536 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 10118247719991024 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 820398463783056 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 186225418159344 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 7302079182096 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 3610204848 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_33531643827487633 : Nat.Prime 33531643827487633 := by
  apply lucas_primality 33531643827487633 (15 : ZMod 33531643827487633)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) = 33531643827487633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_509
      · exact prime_twentyFiveW_1372447766351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 33531643827487633) ^ 16765821913743816 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 11177214609162544 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 65877492784848 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 24432 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_47261873941684471 : Nat.Prime 47261873941684471 := by
  apply lucas_primality 47261873941684471 (19 : ZMod 47261873941684471)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (443, 1), (1185399396581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (443, 1), (1185399396581, 1)] : List FactorBlock).map factorBlockValue).prod) = 47261873941684471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_443
      · exact prime_twentyFiveW_1185399396581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 47261873941684471) ^ 23630936970842235 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 15753957980561490 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 9452374788336894 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 106685945692290 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 39870 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_50375378072400611 : Nat.Prime 50375378072400611 := by
  apply lucas_primality 50375378072400611 (2 : ZMod 50375378072400611)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (70951236721691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (70951236721691, 1)] : List FactorBlock).map factorBlockValue).prod) = 50375378072400611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_71
      · exact prime_twentyFiveW_70951236721691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50375378072400611) ^ 25187689036200305 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 10075075614480122 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 709512367216910 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 710 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_97172129469065243 : Nat.Prime 97172129469065243 := by
  apply lucas_primality 97172129469065243 (2 : ZMod 97172129469065243)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (563, 1), (482114616773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (563, 1), (482114616773, 1)] : List FactorBlock).map factorBlockValue).prod) = 97172129469065243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_179
      · exact prime_twentyFiveW_563
      · exact prime_twentyFiveW_482114616773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97172129469065243) ^ 48586064734532621 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 97172129469065243) ^ 542861058486398 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 97172129469065243) ^ 172597032804734 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 97172129469065243) ^ 201554 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_98917821345979409 : Nat.Prime 98917821345979409 := by
  apply lucas_primality 98917821345979409 (3 : ZMod 98917821345979409)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (347, 1), (6427, 1), (8647, 1), (320591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (347, 1), (6427, 1), (8647, 1), (320591, 1)] : List FactorBlock).map factorBlockValue).prod) = 98917821345979409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_347
      · exact prime_twentyFiveW_6427
      · exact prime_twentyFiveW_8647
      · exact prime_twentyFiveW_320591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 98917821345979409) ^ 49458910672989704 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98917821345979409) ^ 285065767567664 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98917821345979409) ^ 15390978893104 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98917821345979409) ^ 11439553758064 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98917821345979409) ^ 308548341488 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_13421
      · exact prime_twentyFiveW_99611
      · exact prime_twentyFiveW_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_291040469490094697 : Nat.Prime 291040469490094697 := by
  apply lucas_primality 291040469490094697 (3 : ZMod 291040469490094697)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (596394404692817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (596394404692817, 1)] : List FactorBlock).map factorBlockValue).prod) = 291040469490094697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_596394404692817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 291040469490094697) ^ 145520234745047348 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 291040469490094697) ^ 4771155237542536 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 291040469490094697) ^ 488 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_433343651008262639 : Nat.Prime 433343651008262639 := by
  apply lucas_primality 433343651008262639 (7 : ZMod 433343651008262639)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (48439799, 1), (91285969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (48439799, 1), (91285969, 1)] : List FactorBlock).map factorBlockValue).prod) = 433343651008262639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_48439799
      · exact prime_twentyFiveW_91285969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 433343651008262639) ^ 216671825504131319 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 433343651008262639) ^ 61906235858323234 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 433343651008262639) ^ 8946024962 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 433343651008262639) ^ 4747100302 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_61717
      · exact prime_twentyFiveW_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_629218520999394497 : Nat.Prime 629218520999394497 := by
  apply lucas_primality 629218520999394497 (3 : ZMod 629218520999394497)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (504857, 1), (526321871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (504857, 1), (526321871, 1)] : List FactorBlock).map factorBlockValue).prod) = 629218520999394497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_504857
      · exact prime_twentyFiveW_526321871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 629218520999394497) ^ 314609260499697248 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 629218520999394497) ^ 17005905972956608 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 629218520999394497) ^ 1246330190528 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 629218520999394497) ^ 1195501376 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_674243542588974539 : Nat.Prime 674243542588974539 := by
  apply lucas_primality 674243542588974539 (2 : ZMod 674243542588974539)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (329027, 1), (1024602149047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (329027, 1), (1024602149047, 1)] : List FactorBlock).map factorBlockValue).prod) = 674243542588974539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_329027
      · exact prime_twentyFiveW_1024602149047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 674243542588974539) ^ 337121771294487269 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 674243542588974539) ^ 2049204298094 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 674243542588974539) ^ 658054 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1360409812566913403 : Nat.Prime 1360409812566913403 := by
  apply lucas_primality 1360409812566913403 (2 : ZMod 1360409812566913403)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97172129469065243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97172129469065243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1360409812566913403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_97172129469065243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1360409812566913403) ^ 680204906283456701 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1360409812566913403) ^ 194344258938130486 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1360409812566913403) ^ 14 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2482769235797186387 : Nat.Prime 2482769235797186387 := by
  apply lucas_primality 2482769235797186387 (2 : ZMod 2482769235797186387)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (7433440825740079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (7433440825740079, 1)] : List FactorBlock).map factorBlockValue).prod) = 2482769235797186387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_167
      · exact prime_twentyFiveW_7433440825740079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2482769235797186387) ^ 1241384617898593193 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2482769235797186387) ^ 14866881651480158 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2482769235797186387) ^ 334 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2554031246879972731 : Nat.Prime 2554031246879972731 := by
  apply lucas_primality 2554031246879972731 (3 : ZMod 2554031246879972731)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (59, 1), (79, 1), (1405019967587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (59, 1), (79, 1), (1405019967587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554031246879972731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_79
      · exact prime_twentyFiveW_1405019967587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2554031246879972731) ^ 1277015623439986365 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 851343748959990910 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 510806249375994546 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 196463942067690210 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 43288665201355470 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 32329509454176870 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 1817790 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4177836104736762241 : Nat.Prime 4177836104736762241 := by
  apply lucas_primality 4177836104736762241 (26 : ZMod 4177836104736762241)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (510683, 1), (4260874759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (510683, 1), (4260874759, 1)] : List FactorBlock).map factorBlockValue).prod) = 4177836104736762241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_510683
      · exact prime_twentyFiveW_4260874759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 4177836104736762241) ^ 2088918052368381120 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 4177836104736762241) ^ 1392612034912254080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 4177836104736762241) ^ 835567220947352448 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 4177836104736762241) ^ 8180879537280 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 4177836104736762241) ^ 980511360 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_8538352360051590607 : Nat.Prime 8538352360051590607 := by
  apply lucas_primality 8538352360051590607 (3 : ZMod 8538352360051590607)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14033, 1), (101408018718397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14033, 1), (101408018718397, 1)] : List FactorBlock).map factorBlockValue).prod) = 8538352360051590607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_14033
      · exact prime_twentyFiveW_101408018718397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8538352360051590607) ^ 4269176180025795303 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 2846117453350530202 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 608448112310382 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 84198 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_8819147078763676387 : Nat.Prime 8819147078763676387 := by
  apply lucas_primality 8819147078763676387 (2 : ZMod 8819147078763676387)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (3837748946372357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (3837748946372357, 1)] : List FactorBlock).map factorBlockValue).prod) = 8819147078763676387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_383
      · exact prime_twentyFiveW_3837748946372357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8819147078763676387) ^ 4409573539381838193 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819147078763676387) ^ 2939715692921225462 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819147078763676387) ^ 23026493678234142 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819147078763676387) ^ 2298 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_17095130133791526629 : Nat.Prime 17095130133791526629 := by
  apply lucas_primality 17095130133791526629 (2 : ZMod 17095130133791526629)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (19, 1), (12601, 1), (364298788747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (19, 1), (12601, 1), (364298788747, 1)] : List FactorBlock).map factorBlockValue).prod) = 17095130133791526629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_12601
      · exact prime_twentyFiveW_364298788747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17095130133791526629) ^ 8547565066895763314 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17095130133791526629) ^ 2442161447684503804 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17095130133791526629) ^ 899743691252185612 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17095130133791526629) ^ 1356648689293828 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17095130133791526629) ^ 46926124 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_32649835501605921673 : Nat.Prime 32649835501605921673 := by
  apply lucas_primality 32649835501605921673 (5 : ZMod 32649835501605921673)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1360409812566913403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1360409812566913403, 1)] : List FactorBlock).map factorBlockValue).prod) = 32649835501605921673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_1360409812566913403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 32649835501605921673) ^ 16324917750802960836 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 32649835501605921673) ^ 10883278500535307224 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 32649835501605921673) ^ 24 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_41387675792410698833 : Nat.Prime 41387675792410698833 := by
  apply lucas_primality 41387675792410698833 (3 : ZMod 41387675792410698833)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (66533, 1), (5592011, 1), (6952579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (66533, 1), (5592011, 1), (6952579, 1)] : List FactorBlock).map factorBlockValue).prod) = 41387675792410698833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_66533
      · exact prime_twentyFiveW_5592011
      · exact prime_twentyFiveW_6952579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41387675792410698833) ^ 20693837896205349416 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 622062371941904 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 7401215017712 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 5952852285808 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_45023731903529596433 : Nat.Prime 45023731903529596433 := by
  apply lucas_primality 45023731903529596433 (3 : ZMod 45023731903529596433)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) = 45023731903529596433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7411
      · exact prime_twentyFiveW_93287
      · exact prime_twentyFiveW_4070273261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45023731903529596433) ^ 22511865951764798216 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 6075257307182512 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 482636722196336 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 11061599312 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_101627574192727747903 : Nat.Prime 101627574192727747903 := by
  apply lucas_primality 101627574192727747903 (3 : ZMod 101627574192727747903)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) = 101627574192727747903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_3833
      · exact prime_twentyFiveW_1472991480313183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101627574192727747903) ^ 50813787096363873951 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 33875858064242582634 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 26513846645637294 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 68994 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_118104144966714503383 : Nat.Prime 118104144966714503383 := by
  apply lucas_primality 118104144966714503383 (6 : ZMod 118104144966714503383)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (144600413, 1), (594441161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (144600413, 1), (594441161, 1)] : List FactorBlock).map factorBlockValue).prod) = 118104144966714503383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_229
      · exact prime_twentyFiveW_144600413
      · exact prime_twentyFiveW_594441161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118104144966714503383) ^ 59052072483357251691 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118104144966714503383) ^ 39368048322238167794 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118104144966714503383) ^ 515738624308796958 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118104144966714503383) ^ 816762155214 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 118104144966714503383) ^ 198680967462 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_318698601733276800961 : Nat.Prime 318698601733276800961 := by
  apply lucas_primality 318698601733276800961 (11 : ZMod 318698601733276800961)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (10687, 1), (939487, 1), (33064529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (10687, 1), (939487, 1), (33064529, 1)] : List FactorBlock).map factorBlockValue).prod) = 318698601733276800961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_10687
      · exact prime_twentyFiveW_939487
      · exact prime_twentyFiveW_33064529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 318698601733276800961) ^ 159349300866638400480 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 106232867244425600320 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 63739720346655360192 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 29821147350358080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 339226196566080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 9638685666240 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_474232053920584667009 : Nat.Prime 474232053920584667009 := by
  apply lucas_primality 474232053920584667009 (3 : ZMod 474232053920584667009)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (17027, 1), (31084562512099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (17027, 1), (31084562512099, 1)] : List FactorBlock).map factorBlockValue).prod) = 474232053920584667009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_17027
      · exact prime_twentyFiveW_31084562512099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 474232053920584667009) ^ 237116026960292333504 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 67747436274369238144 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 27851768010840704 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 15256192 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_871480771043346770011 : Nat.Prime 871480771043346770011 := by
  apply lucas_primality 871480771043346770011 (12 : ZMod 871480771043346770011)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (61, 1), (4987, 1), (2220746035367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (61, 1), (4987, 1), (2220746035367, 1)] : List FactorBlock).map factorBlockValue).prod) = 871480771043346770011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_61
      · exact prime_twentyFiveW_4987
      · exact prime_twentyFiveW_2220746035367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 871480771043346770011) ^ 435740385521673385005 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 290493590347782256670 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 174296154208669354002 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 20266994675426669070 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 14286570017104045410 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 174750505523029230 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (12 : ZMod 871480771043346770011) ^ 392427030 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_107
      · exact prime_twentyFiveW_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3372843419746565119387 : Nat.Prime 3372843419746565119387 := by
  apply lucas_primality 3372843419746565119387 (2 : ZMod 3372843419746565119387)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (695239, 1), (808557301816729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (695239, 1), (808557301816729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3372843419746565119387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_695239
      · exact prime_twentyFiveW_808557301816729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3372843419746565119387) ^ 1686421709873282559693 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3372843419746565119387) ^ 1124281139915521706462 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3372843419746565119387) ^ 4851343810900374 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3372843419746565119387) ^ 4171434 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_3636586369677809254799 : Nat.Prime 3636586369677809254799 := by
  apply lucas_primality 3636586369677809254799 (7 : ZMod 3636586369677809254799)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (1553, 1), (12866222659007413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (1553, 1), (12866222659007413, 1)] : List FactorBlock).map factorBlockValue).prod) = 3636586369677809254799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_1553
      · exact prime_twentyFiveW_12866222659007413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3636586369677809254799) ^ 1818293184838904627399 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 519512338525401322114 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 279737413052139173446 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 2341652523939349166 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 282646 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5017116660004810029623 : Nat.Prime 5017116660004810029623 := by
  apply lucas_primality 5017116660004810029623 (5 : ZMod 5017116660004810029623)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (698039, 1), (3593722313513149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (698039, 1), (3593722313513149, 1)] : List FactorBlock).map factorBlockValue).prod) = 5017116660004810029623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_698039
      · exact prime_twentyFiveW_3593722313513149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5017116660004810029623) ^ 2508558330002405014811 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5017116660004810029623) ^ 7187444627026298 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5017116660004810029623) ^ 1396078 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_5028074667247311937643 : Nat.Prime 5028074667247311937643 := by
  apply lucas_primality 5028074667247311937643 (6 : ZMod 5028074667247311937643)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (32649835501605921673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (32649835501605921673, 1)] : List FactorBlock).map factorBlockValue).prod) = 5028074667247311937643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_32649835501605921673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5028074667247311937643) ^ 2514037333623655968821 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5028074667247311937643) ^ 718296381035330276806 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5028074667247311937643) ^ 457097697022482903422 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5028074667247311937643) ^ 154 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_10056149334494623875287 : Nat.Prime 10056149334494623875287 := by
  apply lucas_primality 10056149334494623875287 (5 : ZMod 10056149334494623875287)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5028074667247311937643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5028074667247311937643, 1)] : List FactorBlock).map factorBlockValue).prod) = 10056149334494623875287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_5028074667247311937643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10056149334494623875287) ^ 5028074667247311937643 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10056149334494623875287) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_44930152959963511707757 : Nat.Prime 44930152959963511707757 := by
  apply lucas_primality 44930152959963511707757 (2 : ZMod 44930152959963511707757)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (51050897, 1), (2716373653627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (51050897, 1), (2716373653627, 1)] : List FactorBlock).map factorBlockValue).prod) = 44930152959963511707757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_51050897
      · exact prime_twentyFiveW_2716373653627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44930152959963511707757) ^ 22465076479981755853878 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 44930152959963511707757) ^ 14976717653321170569252 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 44930152959963511707757) ^ 880105063775148 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 44930152959963511707757) ^ 16540490628 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_58198922731188676884361 : Nat.Prime 58198922731188676884361 := by
  apply lucas_primality 58198922731188676884361 (7 : ZMod 58198922731188676884361)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (7929133, 1), (2659378548317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (7929133, 1), (2659378548317, 1)] : List FactorBlock).map factorBlockValue).prod) = 58198922731188676884361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_7929133
      · exact prime_twentyFiveW_2659378548317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 58198922731188676884361) ^ 29099461365594338442180 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 19399640910396225628120 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 11639784546237735376872 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 2530387944834290299320 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 7339884793354920 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 21884407080 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_75772932744131311864783 : Nat.Prime 75772932744131311864783 := by
  apply lucas_primality 75772932744131311864783 (3 : ZMod 75772932744131311864783)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (127, 1), (163, 1), (160423, 1), (122671363769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (127, 1), (163, 1), (160423, 1), (122671363769, 1)] : List FactorBlock).map factorBlockValue).prod) = 75772932744131311864783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_127
      · exact prime_twentyFiveW_163
      · exact prime_twentyFiveW_160423
      · exact prime_twentyFiveW_122671363769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75772932744131311864783) ^ 37886466372065655932391 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 25257644248043770621594 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 2444288153036493931122 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 596637265701821353266 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 464864618062155287514 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 472332101657064834 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 617690473278 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_162669220919165630264417 : Nat.Prime 162669220919165630264417 := by
  apply lucas_primality 162669220919165630264417 (3 : ZMod 162669220919165630264417)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43, 1), (191, 1), (197, 1), (3141863835855083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43, 1), (191, 1), (197, 1), (3141863835855083, 1)] : List FactorBlock).map factorBlockValue).prod) = 162669220919165630264417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_191
      · exact prime_twentyFiveW_197
      · exact prime_twentyFiveW_3141863835855083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 162669220919165630264417) ^ 81334610459582815132208 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 162669220919165630264417) ^ 3783005137655014657312 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 162669220919165630264417) ^ 851671313712909058976 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 162669220919165630264417) ^ 825732085884089493728 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 162669220919165630264417) ^ 51774752 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_188146409809226047384267 : Nat.Prime 188146409809226047384267 := by
  apply lucas_primality 188146409809226047384267 (2 : ZMod 188146409809226047384267)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (8387, 1), (15015461856106597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (8387, 1), (15015461856106597, 1)] : List FactorBlock).map factorBlockValue).prod) = 188146409809226047384267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_83
      · exact prime_twentyFiveW_8387
      · exact prime_twentyFiveW_15015461856106597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188146409809226047384267) ^ 94073204904613023692133 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 188146409809226047384267) ^ 62715469936408682461422 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 188146409809226047384267) ^ 2266824214568988522702 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 188146409809226047384267) ^ 22433100013023255918 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 188146409809226047384267) ^ 12530178 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_197526445210116395256319 : Nat.Prime 197526445210116395256319 := by
  apply lucas_primality 197526445210116395256319 (17 : ZMod 197526445210116395256319)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30890258779, 1), (1065742907407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30890258779, 1), (1065742907407, 1)] : List FactorBlock).map factorBlockValue).prod) = 197526445210116395256319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_30890258779
      · exact prime_twentyFiveW_1065742907407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 197526445210116395256319) ^ 98763222605058197628159 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 65842148403372131752106 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 6394457444442 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 185341552674 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_668143682947997302886363 : Nat.Prime 668143682947997302886363 := by
  apply lucas_primality 668143682947997302886363 (2 : ZMod 668143682947997302886363)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (16937033, 1), (857580112926659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (16937033, 1), (857580112926659, 1)] : List FactorBlock).map factorBlockValue).prod) = 668143682947997302886363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_16937033
      · exact prime_twentyFiveW_857580112926659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 668143682947997302886363) ^ 334071841473998651443181 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 29049725345565100125494 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 39448685194626314 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 779103518 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_952396471694610964999163 : Nat.Prime 952396471694610964999163 := by
  apply lucas_primality 952396471694610964999163 (2 : ZMod 952396471694610964999163)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4139, 1), (275415197, 1), (417738454307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4139, 1), (275415197, 1), (417738454307, 1)] : List FactorBlock).map factorBlockValue).prod) = 952396471694610964999163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_4139
      · exact prime_twentyFiveW_275415197
      · exact prime_twentyFiveW_417738454307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 952396471694610964999163) ^ 476198235847305482499581 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 952396471694610964999163) ^ 230103037374875806958 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 952396471694610964999163) ^ 3458038924753346 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 952396471694610964999163) ^ 2279887000766 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1904792943389221929998327 : Nat.Prime 1904792943389221929998327 := by
  apply lucas_primality 1904792943389221929998327 (5 : ZMod 1904792943389221929998327)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (952396471694610964999163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (952396471694610964999163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1904792943389221929998327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_952396471694610964999163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1904792943389221929998327) ^ 952396471694610964999163 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1904792943389221929998327) ^ 2 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4111374614351169382081519 : Nat.Prime 4111374614351169382081519 := by
  apply lucas_primality 4111374614351169382081519 (3 : ZMod 4111374614351169382081519)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (2057275783, 1), (4012963349977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (2057275783, 1), (4012963349977, 1)] : List FactorBlock).map factorBlockValue).prod) = 4111374614351169382081519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_83
      · exact prime_twentyFiveW_2057275783
      · exact prime_twentyFiveW_4012963349977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4111374614351169382081519) ^ 2055687307175584691040759 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4111374614351169382081519) ^ 1370458204783723127360506 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4111374614351169382081519) ^ 49534633907845414241946 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4111374614351169382081519) ^ 1998455748288546 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4111374614351169382081519) ^ 1024523339934 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4762596213756132241022243 : Nat.Prime 4762596213756132241022243 := by
  apply lucas_primality 4762596213756132241022243 (2 : ZMod 4762596213756132241022243)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (44930152959963511707757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (44930152959963511707757, 1)] : List FactorBlock).map factorBlockValue).prod) = 4762596213756132241022243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_44930152959963511707757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4762596213756132241022243) ^ 2381298106878066120511121 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4762596213756132241022243) ^ 89860305919927023415514 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4762596213756132241022243) ^ 106 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_10666428041346285343841227 : Nat.Prime 10666428041346285343841227 := by
  apply lucas_primality 10666428041346285343841227 (2 : ZMod 10666428041346285343841227)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (197526445210116395256319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (197526445210116395256319, 1)] : List FactorBlock).map factorBlockValue).prod) = 10666428041346285343841227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_197526445210116395256319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10666428041346285343841227) ^ 5333214020673142671920613 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10666428041346285343841227) ^ 3555476013782095114613742 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10666428041346285343841227) ^ 54 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_75016934270483646415695533 : Nat.Prime 75016934270483646415695533 := by
  apply lucas_primality 75016934270483646415695533 (2 : ZMod 75016934270483646415695533)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (277, 1), (541, 1), (2554031246879972731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (277, 1), (541, 1), (2554031246879972731, 1)] : List FactorBlock).map factorBlockValue).prod) = 75016934270483646415695533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_277
      · exact prime_twentyFiveW_541
      · exact prime_twentyFiveW_2554031246879972731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75016934270483646415695533) ^ 37508467135241823207847766 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 10716704895783378059385076 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 270819257294164788504316 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 138663464455607479511452 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 29371972 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_314432681942239964763660001 : Nat.Prime 314432681942239964763660001 := by
  apply lucas_primality 314432681942239964763660001 (73 : ZMod 314432681942239964763660001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 314432681942239964763660001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 314432681942239964763660001) ^ 157216340971119982381830000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 104810893980746654921220000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 62886536388447992952732000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 44918954563177137823380000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 28584789267476360433060000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 24187129380172304981820000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 18496040114249409691980000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 16549088523275787619140000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 13670986171401737598420000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 10842506273870343612540000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 10142989740072256927860000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 8498180593033512561180000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 7669089803469267433260000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 7312387952145115459620000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 5932692112117735184220000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 5329367490546440080740000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 314432681942239964763660001) ^ 5154634130200655160060000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_628865363884479929527320001 : Nat.Prime 628865363884479929527320001 := by
  apply lucas_primality 628865363884479929527320001 (97 : ZMod 628865363884479929527320001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 628865363884479929527320001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 628865363884479929527320001) ^ 314432681942239964763660000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 209621787961493309842440000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 125773072776895985905464000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 89837909126354275646760000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 57169578534952720866120000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 48374258760344609963640000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 36992080228498819383960000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 33098177046551575238280000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 27341972342803475196840000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 21685012547740687225080000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 20285979480144513855720000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 16996361186067025122360000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 15338179606938534866520000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 14624775904290230919240000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 11865384224235470368440000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 10658734981092880161480000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 10309268260401310320120000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_757863387245398889430360001 : Nat.Prime 757863387245398889430360001 := by
  apply lucas_primality 757863387245398889430360001 (26 : ZMod 757863387245398889430360001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 4), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 4), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 757863387245398889430360001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 757863387245398889430360001) ^ 378931693622699444715180000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 252621129081799629810120000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 151572677449079777886072000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 108266198177914127061480000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 68896671567763535402760000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 44580199249729346437080000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 39887546697126257338440000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 32950582054147777801320000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 26133220249841341014840000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 24447206040174157723560000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 20482794249875645660280000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 18484472859643875351960000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 17624729935939509056520000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 16124752920114869987880000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 14299309193309413008120000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 12845142156701676092040000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 12423989954842604744760000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1094691559354465062510520003 : Nat.Prime 1094691559354465062510520003 := by
  apply lucas_primality 1094691559354465062510520003 (2 : ZMod 1094691559354465062510520003)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4261, 1), (23005888109, 1), (620395625561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4261, 1), (23005888109, 1), (620395625561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1094691559354465062510520003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_4261
      · exact prime_twentyFiveW_23005888109
      · exact prime_twentyFiveW_620395625561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1094691559354465062510520003) ^ 547345779677232531255260001 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094691559354465062510520003) ^ 364897186451488354170173334 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094691559354465062510520003) ^ 256909542209449674374682 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094691559354465062510520003) ^ 47583103689277578 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094691559354465062510520003) ^ 1764505606184082 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_1642037339031697593765780001 : Nat.Prime 1642037339031697593765780001 := by
  apply lucas_primality 1642037339031697593765780001 (71 : ZMod 1642037339031697593765780001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1642037339031697593765780001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 1642037339031697593765780001) ^ 821018669515848796882890000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 547345779677232531255260000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 328407467806339518753156000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 234576762718813941966540000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 149276121730154326705980000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 126310564540899814905060000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 96590431707746917280340000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 86423017843773557566620000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 71392927783986851902860000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 56621977207989572198820000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 52968946420377341734380000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 44379387541397232263940000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 40049691195895063262580000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 38186914861202269622460000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 34936964660248884973740000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 30981836585503728184260000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 27831141339520298199420000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 26918644902158976946980000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_2686970191142777880707640001 : Nat.Prime 2686970191142777880707640001 := by
  apply lucas_primality 2686970191142777880707640001 (83 : ZMod 2686970191142777880707640001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686970191142777880707640001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 2686970191142777880707640001) ^ 1343485095571388940353820000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 895656730380925960235880000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 537394038228555576141528000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 383852884448968268672520000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 206690014703290606208280000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 158057070067222228276920000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 141419483744356730563560000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 116824790919251212204680000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 92654144522164754507160000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 86676457778799286474440000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 72620815976831834613720000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 65535858320555558066040000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 62487678863785532109480000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 57169578534952720866120000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 50697550776278827937880000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 45541867646487760689960000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 44048691658078325913240000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_4926112017095092781297340001 : Nat.Prime 4926112017095092781297340001 := by
  apply lucas_primality 4926112017095092781297340001 (101 : ZMod 4926112017095092781297340001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4926112017095092781297340001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 4926112017095092781297340001) ^ 2463056008547546390648670000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 1642037339031697593765780000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 985222403419018556259468000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 703730288156441825899620000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 447828365190462980117940000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 378931693622699444715180000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 289771295123240751841020000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 259269053531320672699860000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 214178783351960555708580000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 169865931623968716596460000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 158906839261132025203140000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 133138162624191696791820000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 120149073587685189787740000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 114560744583606808867380000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 104810893980746654921220000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 92945509756511184552780000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 83493424018560894598260000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 80755934706476930840940000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_7389168025642639171946010001 : Nat.Prime 7389168025642639171946010001 := by
  apply lucas_primality 7389168025642639171946010001 (73 : ZMod 7389168025642639171946010001)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389168025642639171946010001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_5
      · exact prime_twentyFiveW_7
      · exact prime_twentyFiveW_11
      · exact prime_twentyFiveW_13
      · exact prime_twentyFiveW_17
      · exact prime_twentyFiveW_19
      · exact prime_twentyFiveW_23
      · exact prime_twentyFiveW_29
      · exact prime_twentyFiveW_31
      · exact prime_twentyFiveW_37
      · exact prime_twentyFiveW_41
      · exact prime_twentyFiveW_43
      · exact prime_twentyFiveW_47
      · exact prime_twentyFiveW_53
      · exact prime_twentyFiveW_59
      · exact prime_twentyFiveW_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 7389168025642639171946010001) ^ 3694584012821319585973005000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 2463056008547546390648670000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 1477833605128527834389202000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 1055595432234662738849430000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 671742547785694470176910000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 568397540434049167072770000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 434656942684861127761530000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 388903580296981009049790000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 321268175027940833562870000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 254798897435953074894690000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 238360258891698037804710000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 199707243936287545187730000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 180223610381527784681610000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 171841116875410213301070000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 157216340971119982381830000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 139418264634766776829170000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 125240136027841341897390000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 121133902059715396261410000 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem prime_twentyFiveW_29556672102570556687784040097 : Nat.Prime 29556672102570556687784040097 := by
  apply lucas_primality 29556672102570556687784040097 (5 : ZMod 29556672102570556687784040097)
  · rw [← twentyFiveWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (710480009, 1), (433343651008262639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (710480009, 1), (433343651008262639, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFiveW_2
      · exact prime_twentyFiveW_3
      · exact prime_twentyFiveW_710480009
      · exact prime_twentyFiveW_433343651008262639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29556672102570556687784040097) ^ 14778336051285278343892020048 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29556672102570556687784040097) ^ 9852224034190185562594680032 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29556672102570556687784040097) ^ 41600990496793213344 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29556672102570556687784040097) ^ 68206080864 ≠ 1
      rw [← twentyFiveWFastPow_eq_pow]
      decide

private theorem phi_twentyFiveW_29556672102570556687784040000 : Nat.totient 29556672102570556687784040000 = 3889284211484015984640000000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_7, prime_twentyFiveW_11, prime_twentyFiveW_13, prime_twentyFiveW_17, prime_twentyFiveW_19, prime_twentyFiveW_23, prime_twentyFiveW_29, prime_twentyFiveW_31, prime_twentyFiveW_37, prime_twentyFiveW_41, prime_twentyFiveW_43, prime_twentyFiveW_47, prime_twentyFiveW_53, prime_twentyFiveW_59, prime_twentyFiveW_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040001 : Nat.totient 29556672102570556687784040001 = 29403528723263640873416573952 := by
  rw [← show ((([(193, 1), (54743994013, 1), (2797446213614389, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_193, prime_twentyFiveW_54743994013, prime_twentyFiveW_2797446213614389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040002 : Nat.totient 29556672102570556687784040002 = 14703319117014794697476324272 := by
  rw [← show ((([(2, 1), (197, 1), (75016934270483646415695533, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_197, prime_twentyFiveW_75016934270483646415695533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040003 : Nat.totient 29556672102570556687784040003 = 19661889818662073510184111840 := by
  rw [← show ((([(3, 1), (463, 1), (422410757, 1), (50375378072400611, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_463, prime_twentyFiveW_422410757, prime_twentyFiveW_50375378072400611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040004 : Nat.totient 29556672102570556687784040004 = 14778336051285278343892020000 := by
  rw [← show ((([(2, 2), (7389168025642639171946010001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_7389168025642639171946010001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040005 : Nat.totient 29556672102570556687784040005 = 23645173098297522210896442048 := by
  rw [← show ((([(5, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_143669, prime_twentyFiveW_13852339783, prime_twentyFiveW_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040006 : Nat.totient 29556672102570556687784040006 = 9852224034190185562594680000 := by
  rw [← show ((([(2, 1), (3, 1), (4926112017095092781297340001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_4926112017095092781297340001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040007 : Nat.totient 29556672102570556687784040007 = 25333735976066079057575439360 := by
  rw [← show ((([(7, 1), (45697, 1), (81709378843, 1), (1130831493331, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_7, prime_twentyFiveW_45697, prime_twentyFiveW_81709378843, prime_twentyFiveW_1130831493331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040008 : Nat.totient 29556672102570556687784040008 = 14625406398706436601212313600 := by
  rw [← show ((([(2, 3), (97, 1), (25411, 1), (152559443, 1), (9825009110321, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_97, prime_twentyFiveW_25411, prime_twentyFiveW_152559443, prime_twentyFiveW_9825009110321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040009 : Nat.totient 29556672102570556687784040009 = 19600920102401723089442880000 := by
  rw [← show ((([(3, 2), (191, 1), (53951, 1), (318698601733276800961, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_191, prime_twentyFiveW_53951, prime_twentyFiveW_318698601733276800961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040010 : Nat.totient 29556672102570556687784040010 = 11767234303164905839260297216 := by
  rw [← show ((([(2, 1), (5, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_223, prime_twentyFiveW_5113, prime_twentyFiveW_101287, prime_twentyFiveW_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040011 : Nat.totient 29556672102570556687784040011 = 26869701911427778807076400000 := by
  rw [← show ((([(11, 1), (2686970191142777880707640001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_11, prime_twentyFiveW_2686970191142777880707640001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040012 : Nat.totient 29556672102570556687784040012 = 9582162583878367276337406720 := by
  rw [← show ((([(2, 2), (3, 1), (67, 1), (79, 1), (58789, 1), (2049369011, 1), (3862390283, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_67, prime_twentyFiveW_79, prime_twentyFiveW_58789, prime_twentyFiveW_2049369011, prime_twentyFiveW_3862390283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040013 : Nat.totient 29556672102570556687784040013 = 27283038301797923885774400048 := by
  rw [← show ((([(13, 1), (625199, 1), (3636586369677809254799, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_13, prime_twentyFiveW_625199, prime_twentyFiveW_3636586369677809254799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040014 : Nat.totient 29556672102570556687784040014 = 12566151111597026225690419200 := by
  rw [← show ((([(2, 1), (7, 1), (149, 1), (997, 1), (4259, 1), (36013, 1), (211441, 1), (438217711, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_7, prime_twentyFiveW_149, prime_twentyFiveW_997, prime_twentyFiveW_4259, prime_twentyFiveW_36013, prime_twentyFiveW_211441, prime_twentyFiveW_438217711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040015 : Nat.totient 29556672102570556687784040015 = 15547617939473564325614668800 := by
  rw [← show ((([(3, 1), (5, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_73, prime_twentyFiveW_13737811, prime_twentyFiveW_68784581, prime_twentyFiveW_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040016 : Nat.totient 29556672102570556687784040016 = 14777870459903428834476691200 := by
  rw [← show ((([(2, 4), (31741, 1), (58198922731188676884361, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_31741, prime_twentyFiveW_58198922731188676884361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040017 : Nat.totient 29556672102570556687784040017 = 27647381483169571611236457792 := by
  rw [← show ((([(17, 1), (163, 1), (10666428041346285343841227, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_17, prime_twentyFiveW_163, prime_twentyFiveW_10666428041346285343841227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040018 : Nat.totient 29556672102570556687784040018 = 9852224034190185562594680000 := by
  rw [← show ((([(2, 1), (3, 2), (1642037339031697593765780001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_1642037339031697593765780001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040019 : Nat.totient 29556672102570556687784040019 = 27996095614335952797785145600 := by
  rw [← show ((([(19, 1), (6871, 1), (32491, 1), (1109609, 1), (6279845155949, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_19, prime_twentyFiveW_6871, prime_twentyFiveW_32491, prime_twentyFiveW_1109609, prime_twentyFiveW_6279845155949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040020 : Nat.totient 29556672102570556687784040020 = 11822668841028222675113616000 := by
  rw [← show ((([(2, 2), (5, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040021 : Nat.totient 29556672102570556687784040021 = 16817888982118899855498624000 := by
  rw [← show ((([(3, 1), (7, 1), (269, 1), (1901, 1), (248528221, 1), (11074551087949, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_7, prime_twentyFiveW_269, prime_twentyFiveW_1901, prime_twentyFiveW_248528221, prime_twentyFiveW_11074551087949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040022 : Nat.totient 29556672102570556687784040022 = 13431413963065921019324640000 := by
  rw [← show ((([(2, 1), (11, 1), (3911, 1), (7268321, 1), (47261873941684471, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_11, prime_twentyFiveW_3911, prime_twentyFiveW_7268321, prime_twentyFiveW_47261873941684471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040023 : Nat.totient 29556672102570556687784040023 = 27961068808588633476433145856 := by
  rw [← show ((([(23, 1), (167, 1), (199, 1), (1273889, 1), (30354743159973073, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_23, prime_twentyFiveW_167, prime_twentyFiveW_199, prime_twentyFiveW_1273889, prime_twentyFiveW_30354743159973073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040024 : Nat.totient 29556672102570556687784040024 = 9852220240333754197896568832 := by
  rw [← show ((([(2, 3), (3, 1), (2596889, 1), (474232053920584667009, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_2596889, prime_twentyFiveW_474232053920584667009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040025 : Nat.totient 29556672102570556687784040025 = 23411096557065912790019523840 := by
  rw [← show ((([(5, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_103, prime_twentyFiveW_5009, prime_twentyFiveW_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040026 : Nat.totient 29556672102570556687784040026 = 13640261618754833923164560256 := by
  rw [← show ((([(2, 1), (13, 1), (10687, 1), (4719079, 1), (22540789770483337, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_13, prime_twentyFiveW_10687, prime_twentyFiveW_4719079, prime_twentyFiveW_22540789770483337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040027 : Nat.totient 29556672102570556687784040027 = 19703084155590976761575533896 := by
  rw [← show ((([(3, 3), (14447, 1), (75772932744131311864783, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_14447, prime_twentyFiveW_75772932744131311864783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040028 : Nat.totient 29556672102570556687784040028 = 12667145186812418430578531184 := by
  rw [← show ((([(2, 2), (7, 1), (3628626968867, 1), (290907674250203, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_7, prime_twentyFiveW_3628626968867, prime_twentyFiveW_290907674250203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040029 : Nat.totient 29556672102570556687784040029 = 28537475065004050703441666496 := by
  rw [← show ((([(29, 1), (21268679, 1), (269471693, 1), (177829524883, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_29, prime_twentyFiveW_21268679, prime_twentyFiveW_269471693, prime_twentyFiveW_177829524883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040030 : Nat.totient 29556672102570556687784040030 = 7841024215338702655066963968 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_283, prime_twentyFiveW_613, prime_twentyFiveW_85303, prime_twentyFiveW_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040031 : Nat.totient 29556672102570556687784040031 = 28583186756515324617478566360 := by
  rw [← show ((([(31, 1), (1427, 1), (668143682947997302886363, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_31, prime_twentyFiveW_1427, prime_twentyFiveW_668143682947997302886363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040032 : Nat.totient 29556672102570556687784040032 = 14764002068652786520400901120 := by
  rw [← show ((([(2, 5), (1031, 1), (428348173229, 1), (2091461964649, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_1031, prime_twentyFiveW_428348173229, prime_twentyFiveW_2091461964649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040033 : Nat.totient 29556672102570556687784040033 = 17912756938720319253071683200 := by
  rw [← show ((([(3, 1), (11, 1), (47431, 1), (10834859807, 1), (1742833970153, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_11, prime_twentyFiveW_47431, prime_twentyFiveW_10834859807, prime_twentyFiveW_1742833970153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040034 : Nat.totient 29556672102570556687784040034 = 13888222457929211492042342400 := by
  rw [← show ((([(2, 1), (17, 1), (937, 1), (2333, 1), (6786591521, 1), (58596351661, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_17, prime_twentyFiveW_937, prime_twentyFiveW_2333, prime_twentyFiveW_6786591521, prime_twentyFiveW_58596351661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040035 : Nat.totient 29556672102570556687784040035 = 20087705161651515460698931200 := by
  rw [← show ((([(5, 1), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_7, prime_twentyFiveW_113, prime_twentyFiveW_54421, prime_twentyFiveW_97654321, prime_twentyFiveW_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040036 : Nat.totient 29556672102570556687784040036 = 9848333765268842706562452480 := by
  rw [← show ((([(2, 2), (3, 2), (4999, 1), (6793, 1), (20983, 1), (1152234038950921, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_4999, prime_twentyFiveW_6793, prime_twentyFiveW_20983, prime_twentyFiveW_1152234038950921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040037 : Nat.totient 29556672102570556687784040037 = 28751715492870691879150739328 := by
  rw [← show ((([(37, 1), (7559, 1), (12377, 1), (8538352360051590607, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_37, prime_twentyFiveW_7559, prime_twentyFiveW_12377, prime_twentyFiveW_8538352360051590607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040038 : Nat.totient 29556672102570556687784040038 = 14000528890681618296473542656 := by
  rw [← show ((([(2, 1), (19, 1), (1447535876737, 1), (537331870728673, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_19, prime_twentyFiveW_1447535876737, prime_twentyFiveW_537331870728673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040039 : Nat.totient 29556672102570556687784040039 = 18188721293889573346328640000 := by
  rw [← show ((([(3, 1), (13, 1), (757863387245398889430360001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_13, prime_twentyFiveW_757863387245398889430360001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040040 : Nat.totient 29556672102570556687784040040 = 11680218790863874308291942400 := by
  rw [← show ((([(2, 3), (5, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_83, prime_twentyFiveW_1433741, prime_twentyFiveW_106163831, prime_twentyFiveW_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040041 : Nat.totient 29556672102570556687784040041 = 28835576976378045356650667680 := by
  rw [← show ((([(41, 1), (143687, 1), (5017116660004810029623, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_41, prime_twentyFiveW_143687, prime_twentyFiveW_5017116660004810029623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040042 : Nat.totient 29556672102570556687784040042 = 8444758164015013293621504960 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1791037, 1), (14588891, 1), (26932669760303, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_7, prime_twentyFiveW_1791037, prime_twentyFiveW_14588891, prime_twentyFiveW_26932669760303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040043 : Nat.totient 29556672102570556687784040043 = 28594294780977697219505971200 := by
  rw [← show ((([(43, 1), (179, 1), (271, 1), (3677, 1), (1467937, 1), (2625207939961, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_43, prime_twentyFiveW_179, prime_twentyFiveW_271, prime_twentyFiveW_3677, prime_twentyFiveW_1467937, prime_twentyFiveW_2625207939961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040044 : Nat.totient 29556672102570556687784040044 = 13434850127960373554999613440 := by
  rw [← show ((([(2, 2), (11, 1), (16230497, 1), (41387675792410698833, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_11, prime_twentyFiveW_16230497, prime_twentyFiveW_41387675792410698833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040045 : Nat.totient 29556672102570556687784040045 = 15735419455154738074399153152 := by
  rw [← show ((([(3, 2), (5, 1), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_569, prime_twentyFiveW_37039, prime_twentyFiveW_1544987, prime_twentyFiveW_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040046 : Nat.totient 29556672102570556687784040046 = 14131623070577419952058201600 := by
  rw [← show ((([(2, 1), (23, 1), (5779, 1), (8167, 1), (624578257, 1), (21796943101, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_23, prime_twentyFiveW_5779, prime_twentyFiveW_8167, prime_twentyFiveW_624578257, prime_twentyFiveW_21796943101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040047 : Nat.totient 29556672102570556687784040047 = 28927806738686076758256720000 := by
  rw [← show ((([(47, 1), (628865363884479929527320001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_47, prime_twentyFiveW_628865363884479929527320001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040048 : Nat.totient 29556672102570556687784040048 = 9750611043097848074672435200 := by
  rw [← show ((([(2, 4), (3, 1), (101, 1), (2399, 1), (129334193, 1), (19649401054343, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_101, prime_twentyFiveW_2399, prime_twentyFiveW_129334193, prime_twentyFiveW_19649401054343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040049 : Nat.totient 29556672102570556687784040049 = 25334290361408205926755031424 := by
  rw [← show ((([(7, 2), (2072555033, 1), (291040469490094697, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_7, prime_twentyFiveW_2072555033, prime_twentyFiveW_291040469490094697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040050 : Nat.totient 29556672102570556687784040050 = 11822668831358244907644122000 := by
  rw [← show ((([(2, 1), (5, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_1222615931, prime_twentyFiveW_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040051 : Nat.totient 29556672102570556687784040051 = 18421979015224101609127065600 := by
  rw [← show ((([(3, 1), (17, 1), (151, 1), (32497, 1), (118104144966714503383, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_17, prime_twentyFiveW_151, prime_twentyFiveW_32497, prime_twentyFiveW_118104144966714503383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040052 : Nat.totient 29556672102570556687784040052 = 13627044114937398433464048000 := by
  rw [← show ((([(2, 2), (13, 1), (941, 1), (506923540391, 1), (1191571499971, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_13, prime_twentyFiveW_941, prime_twentyFiveW_506923540391, prime_twentyFiveW_1191571499971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040053 : Nat.totient 29556672102570556687784040053 = 28949570280533701370641904640 := by
  rw [← show ((([(53, 1), (587, 1), (1087159, 1), (360933317, 1), (2421149041, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_53, prime_twentyFiveW_587, prime_twentyFiveW_1087159, prime_twentyFiveW_360933317, prime_twentyFiveW_2421149041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040054 : Nat.totient 29556672102570556687784040054 = 9849911847866276262912057600 := by
  rw [← show ((([(2, 1), (3, 5), (4261, 1), (23005888109, 1), (620395625561, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_4261, prime_twentyFiveW_23005888109, prime_twentyFiveW_620395625561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040055 : Nat.totient 29556672102570556687784040055 = 21193004323712220233467833600 := by
  rw [← show ((([(5, 1), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_11, prime_twentyFiveW_71, prime_twentyFiveW_26687336297, prime_twentyFiveW_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040056 : Nat.totient 29556672102570556687784040056 = 12524817710677209788948106240 := by
  rw [← show ((([(2, 3), (7, 1), (89, 1), (5881403741, 1), (1008315646774549, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_7, prime_twentyFiveW_89, prime_twentyFiveW_5881403741, prime_twentyFiveW_1008315646774549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040057 : Nat.totient 29556672102570556687784040057 = 18666906198019644249634839552 := by
  rw [← show ((([(3, 1), (19, 1), (40093, 1), (342746533, 1), (37734539424529, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_19, prime_twentyFiveW_40093, prime_twentyFiveW_342746533, prime_twentyFiveW_37734539424529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040058 : Nat.totient 29556672102570556687784040058 = 14135385562428200491354014256 := by
  rw [← show ((([(2, 1), (29, 1), (107, 1), (4762596213756132241022243, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_29, prime_twentyFiveW_107, prime_twentyFiveW_4762596213756132241022243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040059 : Nat.totient 29556672102570556687784040059 = 28945233567742616448254561896 := by
  rw [← show ((([(59, 1), (263, 1), (1904792943389221929998327, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_59, prime_twentyFiveW_263, prime_twentyFiveW_1904792943389221929998327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040060 : Nat.totient 29556672102570556687784040060 = 7809459068838695435749075968 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_109, prime_twentyFiveW_762563, prime_twentyFiveW_500452427, prime_twentyFiveW_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040061 : Nat.totient 29556672102570556687784040061 = 29072135965182870373621337520 := by
  rw [← show ((([(61, 1), (54941323, 1), (8819147078763676387, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_61, prime_twentyFiveW_54941323, prime_twentyFiveW_8819147078763676387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040062 : Nat.totient 29556672102570556687784040062 = 14207958706195619742912912000 := by
  rw [← show ((([(2, 1), (31, 1), (157, 1), (9781, 1), (12791, 1), (24270372050913383, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_31, prime_twentyFiveW_157, prime_twentyFiveW_9781, prime_twentyFiveW_12791, prime_twentyFiveW_24270372050913383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040063 : Nat.totient 29556672102570556687784040063 = 16801525427373924014580249600 := by
  rw [← show ((([(3, 2), (7, 1), (349, 1), (431, 1), (31531, 1), (98917821345979409, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_7, prime_twentyFiveW_349, prime_twentyFiveW_431, prime_twentyFiveW_31531, prime_twentyFiveW_98917821345979409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040064 : Nat.totient 29556672102570556687784040064 = 14778333665944006904866391040 := by
  rw [← show ((([(2, 7), (6215987, 1), (2101226821, 1), (17679196819, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_6215987, prime_twentyFiveW_2101226821, prime_twentyFiveW_17679196819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040065 : Nat.totient 29556672102570556687784040065 = 21777351190298243624308224000 := by
  rw [← show ((([(5, 1), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_13, prime_twentyFiveW_599, prime_twentyFiveW_1811, prime_twentyFiveW_33809, prime_twentyFiveW_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040066 : Nat.totient 29556672102570556687784040066 = 8953313919390876289753456640 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (2753, 1), (162669220919165630264417, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_11, prime_twentyFiveW_2753, prime_twentyFiveW_162669220919165630264417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040067 : Nat.totient 29556672102570556687784040067 = 29556442025102044987130757600 := by
  rw [← show ((([(128467, 1), (5503306021, 1), (41806160925181, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_128467, prime_twentyFiveW_5503306021, prime_twentyFiveW_41806160925181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040068 : Nat.totient 29556672102570556687784040068 = 13908700369136852260403567744 := by
  rw [← show ((([(2, 2), (17, 1), (43223, 1), (10056149334494623875287, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_17, prime_twentyFiveW_43223, prime_twentyFiveW_10056149334494623875287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040069 : Nat.totient 29556672102570556687784040069 = 18847262931243093207559835136 := by
  rw [← show ((([(3, 1), (23, 1), (56923, 1), (254437, 1), (290767, 1), (101716938553, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_23, prime_twentyFiveW_56923, prime_twentyFiveW_254437, prime_twentyFiveW_290767, prime_twentyFiveW_101716938553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040070 : Nat.totient 29556672102570556687784040070 = 10133716143389275870640042496 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_7, prime_twentyFiveW_1671268889, prime_twentyFiveW_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040071 : Nat.totient 29556672102570556687784040071 = 29556671231089785644403354600 := by
  rw [← show ((([(33915461, 1), (871480771043346770011, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_33915461, prime_twentyFiveW_871480771043346770011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040072 : Nat.totient 29556672102570556687784040072 = 9851553155309156414186342400 := by
  rw [← show ((([(2, 3), (3, 2), (15451, 1), (304049, 1), (11825117, 1), (7389540247, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_15451, prime_twentyFiveW_304049, prime_twentyFiveW_11825117, prime_twentyFiveW_7389540247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040073 : Nat.totient 29556672102570556687784040073 = 29522423337183633898902558528 := by
  rw [← show ((([(863, 1), (2050309799, 1), (16704183438336529, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_863, prime_twentyFiveW_2050309799, prime_twentyFiveW_16704183438336529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040074 : Nat.totient 29556672102570556687784040074 = 14319027437018454156817022976 := by
  rw [← show ((([(2, 1), (37, 1), (257, 1), (6607, 1), (8059, 1), (136344823, 1), (214075307, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_37, prime_twentyFiveW_257, prime_twentyFiveW_6607, prime_twentyFiveW_8059, prime_twentyFiveW_136344823, prime_twentyFiveW_214075307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040075 : Nat.totient 29556672102570556687784040075 = 15763558454704296900151488000 := by
  rw [← show ((([(3, 1), (5, 2), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040076 : Nat.totient 29556672102570556687784040076 = 14000528866418548771824561744 := by
  rw [← show ((([(2, 2), (19, 1), (576799859, 1), (674243542588974539, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_19, prime_twentyFiveW_576799859, prime_twentyFiveW_674243542588974539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040077 : Nat.totient 29556672102570556687784040077 = 23031021688196665070405649600 := by
  rw [← show ((([(7, 1), (11, 1), (205847, 1), (595571, 1), (55149007, 1), (56773939, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_7, prime_twentyFiveW_11, prime_twentyFiveW_205847, prime_twentyFiveW_595571, prime_twentyFiveW_55149007, prime_twentyFiveW_56773939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040078 : Nat.totient 29556672102570556687784040078 = 9094357869910405957177650432 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (5845319, 1), (7447087, 1), (8704950107417, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_13, prime_twentyFiveW_5845319, prime_twentyFiveW_7447087, prime_twentyFiveW_8704950107417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040079 : Nat.totient 29556672102570556687784040079 = 29020688889148043121752388000 := by
  rw [← show ((([(67, 1), (307, 1), (26391775451, 1), (54446974002341, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_67, prime_twentyFiveW_307, prime_twentyFiveW_26391775451, prime_twentyFiveW_54446974002341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040080 : Nat.totient 29556672102570556687784040080 = 11822668813725037826480400384 := by
  rw [← show ((([(2, 4), (5, 1), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_5, prime_twentyFiveW_433014277, prime_twentyFiveW_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040081 : Nat.totient 29556672102570556687784040081 = 19704448068380371125189360036 := by
  rw [← show ((([(3, 3), (1094691559354465062510520003, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_1094691559354465062510520003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040082 : Nat.totient 29556672102570556687784040082 = 14402853899622673825306936320 := by
  rw [← show ((([(2, 1), (41, 1), (983, 1), (39209, 1), (40653499, 1), (230040586717, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_41, prime_twentyFiveW_983, prime_twentyFiveW_39209, prime_twentyFiveW_40653499, prime_twentyFiveW_230040586717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040083 : Nat.totient 29556672102570556687784040083 = 29552920069701112129694391880 := by
  rw [← show ((([(7919, 1), (1503311, 1), (2482769235797186387, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_7919, prime_twentyFiveW_1503311, prime_twentyFiveW_2482769235797186387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040084 : Nat.totient 29556672102570556687784040084 = 8444682509635227993230071008 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (104323, 1), (3372843419746565119387, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_7, prime_twentyFiveW_104323, prime_twentyFiveW_3372843419746565119387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040085 : Nat.totient 29556672102570556687784040085 = 22254428961300141406595490048 := by
  rw [← show ((([(5, 1), (17, 1), (3421567, 1), (101627574192727747903, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_17, prime_twentyFiveW_3421567, prime_twentyFiveW_101627574192727747903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040086 : Nat.totient 29556672102570556687784040086 = 14369343598374509215776160800 := by
  rw [← show ((([(2, 1), (43, 1), (347, 1), (607, 1), (2860615019, 1), (570399980551, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_43, prime_twentyFiveW_347, prime_twentyFiveW_607, prime_twentyFiveW_2860615019, prime_twentyFiveW_570399980551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040087 : Nat.totient 29556672102570556687784040087 = 18946042317773551967087700480 := by
  rw [← show ((([(3, 1), (29, 1), (241, 1), (105040643, 1), (13420288955312027, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_29, prime_twentyFiveW_241, prime_twentyFiveW_105040643, prime_twentyFiveW_13420288955312027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040088 : Nat.totient 29556672102570556687784040088 = 13230019408700574168143938560 := by
  rw [← show ((([(2, 3), (11, 1), (73, 1), (823, 1), (2927, 1), (77699, 1), (24581705669203, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_11, prime_twentyFiveW_73, prime_twentyFiveW_823, prime_twentyFiveW_2927, prime_twentyFiveW_77699, prime_twentyFiveW_24581705669203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040089 : Nat.totient 29556672102570556687784040089 = 29319882309453239979481144320 := by
  rw [← show ((([(137, 1), (1721, 1), (7333, 1), (17095130133791526629, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_137, prime_twentyFiveW_1721, prime_twentyFiveW_7333, prime_twentyFiveW_17095130133791526629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040090 : Nat.totient 29556672102570556687784040090 = 7881778146782582765190371328 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7294097, 1), (45023731903529596433, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_5, prime_twentyFiveW_7294097, prime_twentyFiveW_45023731903529596433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040091 : Nat.totient 29556672102570556687784040091 = 23089479834196167249769805088 := by
  rw [← show ((([(7, 1), (13, 1), (79, 1), (4111374614351169382081519, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_7, prime_twentyFiveW_13, prime_twentyFiveW_79, prime_twentyFiveW_4111374614351169382081519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040092 : Nat.totient 29556672102570556687784040092 = 14128095209880278728418583552 := by
  rw [← show ((([(2, 2), (23, 1), (1847, 1), (276439, 1), (629218520999394497, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_23, prime_twentyFiveW_1847, prime_twentyFiveW_276439, prime_twentyFiveW_629218520999394497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040093 : Nat.totient 29556672102570556687784040093 = 19068820460665676735606784000 := by
  rw [← show ((([(3, 1), (31, 1), (76071361, 1), (4177836104736762241, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_31, prime_twentyFiveW_76071361, prime_twentyFiveW_4177836104736762241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040094 : Nat.totient 29556672102570556687784040094 = 14463903369343038379128360000 := by
  rw [← show ((([(2, 1), (47, 1), (314432681942239964763660001, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_47, prime_twentyFiveW_314432681942239964763660001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040095 : Nat.totient 29556672102570556687784040095 = 22400846222691827097637853184 := by
  rw [← show ((([(5, 1), (19, 1), (9278485297, 1), (33531643827487633, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_5, prime_twentyFiveW_19, prime_twentyFiveW_9278485297, prime_twentyFiveW_33531643827487633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040096 : Nat.totient 29556672102570556687784040096 = 9852224020323188707594915328 := by
  rw [← show ((([(2, 5), (3, 1), (710480009, 1), (433343651008262639, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_3, prime_twentyFiveW_710480009, prime_twentyFiveW_433343651008262639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040097 : Nat.totient 29556672102570556687784040097 = 29556672102570556687784040096 := by
  rw [← show ((([(29556672102570556687784040097, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_29556672102570556687784040097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040098 : Nat.totient 29556672102570556687784040098 = 12611830142332040408262118512 := by
  rw [← show ((([(2, 1), (7, 3), (229, 1), (188146409809226047384267, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_2, prime_twentyFiveW_7, prime_twentyFiveW_229, prime_twentyFiveW_188146409809226047384267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFiveW_29556672102570556687784040099 : Nat.totient 29556672102570556687784040099 = 17725379300994247252875648000 := by
  rw [← show ((([(3, 2), (11, 2), (131, 1), (353, 1), (27031, 1), (21712985397389927, 1)] : List FactorBlock).map factorBlockValue).prod) = 29556672102570556687784040099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFiveW_3, prime_twentyFiveW_11, prime_twentyFiveW_131, prime_twentyFiveW_353, prime_twentyFiveW_27031, prime_twentyFiveW_21712985397389927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyFiveW : certifiedKill 1 29556672102570556687784039999 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyFiveW_29556672102570556687784040000, phi_twentyFiveW_29556672102570556687784040001, phi_twentyFiveW_29556672102570556687784040002,
    phi_twentyFiveW_29556672102570556687784040003, phi_twentyFiveW_29556672102570556687784040004, phi_twentyFiveW_29556672102570556687784040005,
    phi_twentyFiveW_29556672102570556687784040006, phi_twentyFiveW_29556672102570556687784040007, phi_twentyFiveW_29556672102570556687784040008,
    phi_twentyFiveW_29556672102570556687784040009, phi_twentyFiveW_29556672102570556687784040010, phi_twentyFiveW_29556672102570556687784040011,
    phi_twentyFiveW_29556672102570556687784040012, phi_twentyFiveW_29556672102570556687784040013, phi_twentyFiveW_29556672102570556687784040014,
    phi_twentyFiveW_29556672102570556687784040015, phi_twentyFiveW_29556672102570556687784040016, phi_twentyFiveW_29556672102570556687784040017,
    phi_twentyFiveW_29556672102570556687784040018, phi_twentyFiveW_29556672102570556687784040019, phi_twentyFiveW_29556672102570556687784040020,
    phi_twentyFiveW_29556672102570556687784040021, phi_twentyFiveW_29556672102570556687784040022, phi_twentyFiveW_29556672102570556687784040023,
    phi_twentyFiveW_29556672102570556687784040024, phi_twentyFiveW_29556672102570556687784040025, phi_twentyFiveW_29556672102570556687784040026,
    phi_twentyFiveW_29556672102570556687784040027, phi_twentyFiveW_29556672102570556687784040028, phi_twentyFiveW_29556672102570556687784040029,
    phi_twentyFiveW_29556672102570556687784040030, phi_twentyFiveW_29556672102570556687784040031, phi_twentyFiveW_29556672102570556687784040032,
    phi_twentyFiveW_29556672102570556687784040033, phi_twentyFiveW_29556672102570556687784040034, phi_twentyFiveW_29556672102570556687784040035,
    phi_twentyFiveW_29556672102570556687784040036, phi_twentyFiveW_29556672102570556687784040037, phi_twentyFiveW_29556672102570556687784040038,
    phi_twentyFiveW_29556672102570556687784040039, phi_twentyFiveW_29556672102570556687784040040, phi_twentyFiveW_29556672102570556687784040041,
    phi_twentyFiveW_29556672102570556687784040042, phi_twentyFiveW_29556672102570556687784040043, phi_twentyFiveW_29556672102570556687784040044,
    phi_twentyFiveW_29556672102570556687784040045, phi_twentyFiveW_29556672102570556687784040046, phi_twentyFiveW_29556672102570556687784040047,
    phi_twentyFiveW_29556672102570556687784040048, phi_twentyFiveW_29556672102570556687784040049, phi_twentyFiveW_29556672102570556687784040050,
    phi_twentyFiveW_29556672102570556687784040051, phi_twentyFiveW_29556672102570556687784040052, phi_twentyFiveW_29556672102570556687784040053,
    phi_twentyFiveW_29556672102570556687784040054, phi_twentyFiveW_29556672102570556687784040055, phi_twentyFiveW_29556672102570556687784040056,
    phi_twentyFiveW_29556672102570556687784040057, phi_twentyFiveW_29556672102570556687784040058, phi_twentyFiveW_29556672102570556687784040059,
    phi_twentyFiveW_29556672102570556687784040060, phi_twentyFiveW_29556672102570556687784040061, phi_twentyFiveW_29556672102570556687784040062,
    phi_twentyFiveW_29556672102570556687784040063, phi_twentyFiveW_29556672102570556687784040064, phi_twentyFiveW_29556672102570556687784040065,
    phi_twentyFiveW_29556672102570556687784040066, phi_twentyFiveW_29556672102570556687784040067, phi_twentyFiveW_29556672102570556687784040068,
    phi_twentyFiveW_29556672102570556687784040069, phi_twentyFiveW_29556672102570556687784040070, phi_twentyFiveW_29556672102570556687784040071,
    phi_twentyFiveW_29556672102570556687784040072, phi_twentyFiveW_29556672102570556687784040073, phi_twentyFiveW_29556672102570556687784040074,
    phi_twentyFiveW_29556672102570556687784040075, phi_twentyFiveW_29556672102570556687784040076, phi_twentyFiveW_29556672102570556687784040077,
    phi_twentyFiveW_29556672102570556687784040078, phi_twentyFiveW_29556672102570556687784040079, phi_twentyFiveW_29556672102570556687784040080,
    phi_twentyFiveW_29556672102570556687784040081, phi_twentyFiveW_29556672102570556687784040082, phi_twentyFiveW_29556672102570556687784040083,
    phi_twentyFiveW_29556672102570556687784040084, phi_twentyFiveW_29556672102570556687784040085, phi_twentyFiveW_29556672102570556687784040086,
    phi_twentyFiveW_29556672102570556687784040087, phi_twentyFiveW_29556672102570556687784040088, phi_twentyFiveW_29556672102570556687784040089,
    phi_twentyFiveW_29556672102570556687784040090, phi_twentyFiveW_29556672102570556687784040091, phi_twentyFiveW_29556672102570556687784040092,
    phi_twentyFiveW_29556672102570556687784040093, phi_twentyFiveW_29556672102570556687784040094, phi_twentyFiveW_29556672102570556687784040095,
    phi_twentyFiveW_29556672102570556687784040096, phi_twentyFiveW_29556672102570556687784040097, phi_twentyFiveW_29556672102570556687784040098,
    phi_twentyFiveW_29556672102570556687784040099]

end TotientTailPeriodKiller
end Erdos249257
