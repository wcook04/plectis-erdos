import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def decHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem decHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    decHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [decHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [decHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then decHFastPow a n * decHFastPow a n * a
        else decHFastPow a n * decHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_decH_2 : Nat.Prime 2 := by norm_num
private theorem prime_decH_3 : Nat.Prime 3 := by norm_num
private theorem prime_decH_5 : Nat.Prime 5 := by norm_num
private theorem prime_decH_7 : Nat.Prime 7 := by norm_num
private theorem prime_decH_11 : Nat.Prime 11 := by norm_num
private theorem prime_decH_13 : Nat.Prime 13 := by norm_num
private theorem prime_decH_17 : Nat.Prime 17 := by norm_num
private theorem prime_decH_19 : Nat.Prime 19 := by norm_num
private theorem prime_decH_23 : Nat.Prime 23 := by norm_num
private theorem prime_decH_29 : Nat.Prime 29 := by norm_num
private theorem prime_decH_31 : Nat.Prime 31 := by norm_num
private theorem prime_decH_37 : Nat.Prime 37 := by norm_num
private theorem prime_decH_41 : Nat.Prime 41 := by norm_num
private theorem prime_decH_43 : Nat.Prime 43 := by norm_num
private theorem prime_decH_47 : Nat.Prime 47 := by norm_num
private theorem prime_decH_53 : Nat.Prime 53 := by norm_num
private theorem prime_decH_59 : Nat.Prime 59 := by norm_num
private theorem prime_decH_61 : Nat.Prime 61 := by norm_num
private theorem prime_decH_67 : Nat.Prime 67 := by norm_num
private theorem prime_decH_71 : Nat.Prime 71 := by norm_num
private theorem prime_decH_73 : Nat.Prime 73 := by norm_num
private theorem prime_decH_79 : Nat.Prime 79 := by norm_num
private theorem prime_decH_83 : Nat.Prime 83 := by norm_num
private theorem prime_decH_89 : Nat.Prime 89 := by norm_num
private theorem prime_decH_97 : Nat.Prime 97 := by norm_num
private theorem prime_decH_101 : Nat.Prime 101 := by norm_num
private theorem prime_decH_103 : Nat.Prime 103 := by norm_num
private theorem prime_decH_107 : Nat.Prime 107 := by norm_num
private theorem prime_decH_109 : Nat.Prime 109 := by norm_num
private theorem prime_decH_113 : Nat.Prime 113 := by norm_num
private theorem prime_decH_127 : Nat.Prime 127 := by norm_num
private theorem prime_decH_131 : Nat.Prime 131 := by norm_num
private theorem prime_decH_137 : Nat.Prime 137 := by norm_num
private theorem prime_decH_139 : Nat.Prime 139 := by norm_num
private theorem prime_decH_149 : Nat.Prime 149 := by norm_num
private theorem prime_decH_151 : Nat.Prime 151 := by norm_num
private theorem prime_decH_163 : Nat.Prime 163 := by norm_num
private theorem prime_decH_167 : Nat.Prime 167 := by norm_num
private theorem prime_decH_179 : Nat.Prime 179 := by norm_num
private theorem prime_decH_181 : Nat.Prime 181 := by norm_num
private theorem prime_decH_191 : Nat.Prime 191 := by norm_num
private theorem prime_decH_193 : Nat.Prime 193 := by norm_num
private theorem prime_decH_197 : Nat.Prime 197 := by norm_num
private theorem prime_decH_199 : Nat.Prime 199 := by norm_num
private theorem prime_decH_211 : Nat.Prime 211 := by norm_num
private theorem prime_decH_223 : Nat.Prime 223 := by norm_num
private theorem prime_decH_227 : Nat.Prime 227 := by norm_num
private theorem prime_decH_229 : Nat.Prime 229 := by norm_num
private theorem prime_decH_233 : Nat.Prime 233 := by norm_num
private theorem prime_decH_239 : Nat.Prime 239 := by norm_num
private theorem prime_decH_241 : Nat.Prime 241 := by norm_num
private theorem prime_decH_257 : Nat.Prime 257 := by norm_num
private theorem prime_decH_269 : Nat.Prime 269 := by norm_num
private theorem prime_decH_271 : Nat.Prime 271 := by norm_num
private theorem prime_decH_281 : Nat.Prime 281 := by norm_num
private theorem prime_decH_283 : Nat.Prime 283 := by norm_num
private theorem prime_decH_307 : Nat.Prime 307 := by norm_num
private theorem prime_decH_311 : Nat.Prime 311 := by norm_num
private theorem prime_decH_313 : Nat.Prime 313 := by norm_num
private theorem prime_decH_317 : Nat.Prime 317 := by norm_num
private theorem prime_decH_337 : Nat.Prime 337 := by norm_num
private theorem prime_decH_347 : Nat.Prime 347 := by norm_num
private theorem prime_decH_349 : Nat.Prime 349 := by norm_num
private theorem prime_decH_373 : Nat.Prime 373 := by norm_num
private theorem prime_decH_379 : Nat.Prime 379 := by norm_num
private theorem prime_decH_383 : Nat.Prime 383 := by norm_num
private theorem prime_decH_397 : Nat.Prime 397 := by norm_num
private theorem prime_decH_401 : Nat.Prime 401 := by norm_num
private theorem prime_decH_409 : Nat.Prime 409 := by norm_num
private theorem prime_decH_421 : Nat.Prime 421 := by norm_num
private theorem prime_decH_431 : Nat.Prime 431 := by norm_num
private theorem prime_decH_433 : Nat.Prime 433 := by norm_num
private theorem prime_decH_439 : Nat.Prime 439 := by norm_num
private theorem prime_decH_443 : Nat.Prime 443 := by norm_num
private theorem prime_decH_449 : Nat.Prime 449 := by norm_num
private theorem prime_decH_461 : Nat.Prime 461 := by norm_num
private theorem prime_decH_463 : Nat.Prime 463 := by norm_num
private theorem prime_decH_467 : Nat.Prime 467 := by norm_num
private theorem prime_decH_479 : Nat.Prime 479 := by norm_num
private theorem prime_decH_491 : Nat.Prime 491 := by norm_num
private theorem prime_decH_509 : Nat.Prime 509 := by norm_num
private theorem prime_decH_563 : Nat.Prime 563 := by norm_num
private theorem prime_decH_569 : Nat.Prime 569 := by norm_num
private theorem prime_decH_577 : Nat.Prime 577 := by norm_num
private theorem prime_decH_599 : Nat.Prime 599 := by norm_num
private theorem prime_decH_601 : Nat.Prime 601 := by norm_num
private theorem prime_decH_613 : Nat.Prime 613 := by norm_num
private theorem prime_decH_617 : Nat.Prime 617 := by norm_num
private theorem prime_decH_619 : Nat.Prime 619 := by norm_num
private theorem prime_decH_631 : Nat.Prime 631 := by norm_num
private theorem prime_decH_653 : Nat.Prime 653 := by norm_num
private theorem prime_decH_659 : Nat.Prime 659 := by norm_num
private theorem prime_decH_673 : Nat.Prime 673 := by norm_num
private theorem prime_decH_701 : Nat.Prime 701 := by norm_num
private theorem prime_decH_719 : Nat.Prime 719 := by norm_num
private theorem prime_decH_733 : Nat.Prime 733 := by norm_num
private theorem prime_decH_739 : Nat.Prime 739 := by norm_num
private theorem prime_decH_751 : Nat.Prime 751 := by norm_num
private theorem prime_decH_761 : Nat.Prime 761 := by norm_num
private theorem prime_decH_809 : Nat.Prime 809 := by norm_num
private theorem prime_decH_811 : Nat.Prime 811 := by norm_num
private theorem prime_decH_829 : Nat.Prime 829 := by norm_num
private theorem prime_decH_853 : Nat.Prime 853 := by norm_num
private theorem prime_decH_859 : Nat.Prime 859 := by norm_num
private theorem prime_decH_947 : Nat.Prime 947 := by norm_num
private theorem prime_decH_977 : Nat.Prime 977 := by norm_num
private theorem prime_decH_983 : Nat.Prime 983 := by norm_num
private theorem prime_decH_991 : Nat.Prime 991 := by norm_num
private theorem prime_decH_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_decH_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_decH_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_decH_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_decH_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_decH_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_decH_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_decH_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_decH_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_decH_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_decH_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_decH_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_decH_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_decH_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_decH_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_decH_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_decH_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_decH_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_decH_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_decH_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_decH_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_decH_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_decH_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_decH_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_decH_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_decH_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_decH_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_decH_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_decH_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_decH_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_decH_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_decH_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_decH_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_decH_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_decH_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_decH_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_decH_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_decH_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_decH_3767 : Nat.Prime 3767 := by norm_num
private theorem prime_decH_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_decH_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_decH_4007 : Nat.Prime 4007 := by norm_num
private theorem prime_decH_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_decH_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_decH_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_decH_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_decH_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_decH_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_decH_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_decH_5623 : Nat.Prime 5623 := by norm_num
private theorem prime_decH_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_decH_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_decH_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_decH_5923 : Nat.Prime 5923 := by norm_num
private theorem prime_decH_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_decH_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_decH_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_decH_6221 : Nat.Prime 6221 := by norm_num
private theorem prime_decH_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_decH_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_decH_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_decH_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_decH_6733 : Nat.Prime 6733 := by norm_num
private theorem prime_decH_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_decH_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_decH_7489 : Nat.Prime 7489 := by norm_num
private theorem prime_decH_8221 : Nat.Prime 8221 := by norm_num
private theorem prime_decH_8969 : Nat.Prime 8969 := by norm_num
private theorem prime_decH_9091 : Nat.Prime 9091 := by norm_num
private theorem prime_decH_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_decH_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_decH_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_decH_9871 : Nat.Prime 9871 := by norm_num
private theorem prime_decH_9901 : Nat.Prime 9901 := by norm_num
private theorem prime_decH_10099 : Nat.Prime 10099 := by norm_num
private theorem prime_decH_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_decH_10499 : Nat.Prime 10499 := by norm_num
private theorem prime_decH_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_decH_11261 : Nat.Prime 11261 := by norm_num
private theorem prime_decH_11321 : Nat.Prime 11321 := by norm_num
private theorem prime_decH_12379 : Nat.Prime 12379 := by norm_num
private theorem prime_decH_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_decH_13297 : Nat.Prime 13297 := by norm_num
private theorem prime_decH_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_decH_13669 : Nat.Prime 13669 := by norm_num
private theorem prime_decH_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_decH_14923 : Nat.Prime 14923 := by norm_num
private theorem prime_decH_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_decH_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_decH_18757 : Nat.Prime 18757 := by norm_num
private theorem prime_decH_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_decH_19037 : Nat.Prime 19037 := by norm_num
private theorem prime_decH_19073 : Nat.Prime 19073 := by norm_num
private theorem prime_decH_19183 : Nat.Prime 19183 := by norm_num
private theorem prime_decH_19213 : Nat.Prime 19213 := by norm_num
private theorem prime_decH_19993 : Nat.Prime 19993 := by norm_num
private theorem prime_decH_21121 : Nat.Prime 21121 := by norm_num
private theorem prime_decH_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_decH_22811 : Nat.Prime 22811 := by norm_num
private theorem prime_decH_23857 : Nat.Prime 23857 := by norm_num
private theorem prime_decH_23911 : Nat.Prime 23911 := by norm_num
private theorem prime_decH_25633 : Nat.Prime 25633 := by norm_num
private theorem prime_decH_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_decH_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_decH_30871 : Nat.Prime 30871 := by norm_num
private theorem prime_decH_33809 : Nat.Prime 33809 := by norm_num
private theorem prime_decH_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_decH_34367 : Nat.Prime 34367 := by norm_num
private theorem prime_decH_35023 : Nat.Prime 35023 := by norm_num
private theorem prime_decH_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_decH_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_decH_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_decH_39119 : Nat.Prime 39119 := by norm_num
private theorem prime_decH_40739 : Nat.Prime 40739 := by norm_num
private theorem prime_decH_42337 : Nat.Prime 42337 := by norm_num
private theorem prime_decH_43517 : Nat.Prime 43517 := by norm_num
private theorem prime_decH_45119 : Nat.Prime 45119 := by norm_num
private theorem prime_decH_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_decH_46681 : Nat.Prime 46681 := by norm_num
private theorem prime_decH_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_decH_47837 : Nat.Prime 47837 := by norm_num
private theorem prime_decH_47857 : Nat.Prime 47857 := by norm_num
private theorem prime_decH_48383 : Nat.Prime 48383 := by norm_num
private theorem prime_decH_50753 : Nat.Prime 50753 := by norm_num
private theorem prime_decH_51949 : Nat.Prime 51949 := by norm_num
private theorem prime_decH_52541 : Nat.Prime 52541 := by norm_num
private theorem prime_decH_52579 : Nat.Prime 52579 := by norm_num
private theorem prime_decH_53813 : Nat.Prime 53813 := by norm_num
private theorem prime_decH_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_decH_55001 : Nat.Prime 55001 := by norm_num
private theorem prime_decH_59659 : Nat.Prime 59659 := by norm_num
private theorem prime_decH_61637 : Nat.Prime 61637 := by norm_num
private theorem prime_decH_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_decH_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_decH_68477 : Nat.Prime 68477 := by norm_num
private theorem prime_decH_73547 : Nat.Prime 73547 := by norm_num
private theorem prime_decH_73819 : Nat.Prime 73819 := by norm_num
private theorem prime_decH_76343 : Nat.Prime 76343 := by norm_num
private theorem prime_decH_77489 : Nat.Prime 77489 := by norm_num
private theorem prime_decH_77611 : Nat.Prime 77611 := by norm_num
private theorem prime_decH_80567 : Nat.Prime 80567 := by norm_num
private theorem prime_decH_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_decH_90191 : Nat.Prime 90191 := by norm_num
private theorem prime_decH_93287 : Nat.Prime 93287 := by norm_num
private theorem prime_decH_97387 : Nat.Prime 97387 := by norm_num
private theorem prime_decH_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_decH_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_decH_99611 : Nat.Prime 99611 := by norm_num
private theorem prime_decH_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_decH_108923 : Nat.Prime 108923 := by norm_num
private theorem prime_decH_111767 : Nat.Prime 111767 := by norm_num
private theorem prime_decH_114013 : Nat.Prime 114013 := by norm_num
private theorem prime_decH_115319 : Nat.Prime 115319 := by norm_num
private theorem prime_decH_115901 : Nat.Prime 115901 := by norm_num
private theorem prime_decH_117877 : Nat.Prime 117877 := by norm_num
private theorem prime_decH_118687 : Nat.Prime 118687 := by norm_num
private theorem prime_decH_124459 : Nat.Prime 124459 := by norm_num
private theorem prime_decH_129223 : Nat.Prime 129223 := by norm_num
private theorem prime_decH_129439 : Nat.Prime 129439 := by norm_num
private theorem prime_decH_132233 : Nat.Prime 132233 := by norm_num
private theorem prime_decH_141551 : Nat.Prime 141551 := by norm_num
private theorem prime_decH_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_decH_156521 : Nat.Prime 156521 := by norm_num
private theorem prime_decH_170447 : Nat.Prime 170447 := by norm_num
private theorem prime_decH_179351 : Nat.Prime 179351 := by norm_num
private theorem prime_decH_193261 : Nat.Prime 193261 := by norm_num
private theorem prime_decH_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_decH_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_decH_230189 : Nat.Prime 230189 := by norm_num
private theorem prime_decH_248797 : Nat.Prime 248797 := by norm_num
private theorem prime_decH_266957 : Nat.Prime 266957 := by norm_num
private theorem prime_decH_284957 : Nat.Prime 284957 := by norm_num
private theorem prime_decH_287801 : Nat.Prime 287801 := by norm_num
private theorem prime_decH_301681 : Nat.Prime 301681 := by norm_num
private theorem prime_decH_336253 : Nat.Prime 336253 := by norm_num
private theorem prime_decH_344873 : Nat.Prime 344873 := by norm_num
private theorem prime_decH_363563 : Nat.Prime 363563 := by norm_num
private theorem prime_decH_374681 : Nat.Prime 374681 := by norm_num
private theorem prime_decH_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_decH_505097 : Nat.Prime 505097 := by norm_num
private theorem prime_decH_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_decH_595117 : Nat.Prime 595117 := by norm_num
private theorem prime_decH_609781 : Nat.Prime 609781 := by norm_num
private theorem prime_decH_623279 : Nat.Prime 623279 := by norm_num
private theorem prime_decH_641057 : Nat.Prime 641057 := by norm_num
private theorem prime_decH_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_decH_659237 : Nat.Prime 659237 := by norm_num
private theorem prime_decH_660547 : Nat.Prime 660547 := by norm_num
private theorem prime_decH_685493 : Nat.Prime 685493 := by norm_num
private theorem prime_decH_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_decH_874459 : Nat.Prime 874459 := by norm_num
private theorem prime_decH_895729 : Nat.Prime 895729 := by norm_num
private theorem prime_decH_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_decH_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_decH_972197 : Nat.Prime 972197 := by norm_num
private theorem prime_decH_1044397 : Nat.Prime 1044397 := by norm_num
private theorem prime_decH_1167211 : Nat.Prime 1167211 := by norm_num
private theorem prime_decH_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_decH_1278733 : Nat.Prime 1278733 := by norm_num
private theorem prime_decH_1282511 : Nat.Prime 1282511 := by norm_num
private theorem prime_decH_1334561 : Nat.Prime 1334561 := by norm_num
private theorem prime_decH_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_decH_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_decH_1479571 : Nat.Prime 1479571 := by norm_num
private theorem prime_decH_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_decH_1726787 : Nat.Prime 1726787 := by norm_num
private theorem prime_decH_1814357 : Nat.Prime 1814357 := by norm_num
private theorem prime_decH_1833389 : Nat.Prime 1833389 := by norm_num
private theorem prime_decH_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_decH_1997173 : Nat.Prime 1997173 := by norm_num
private theorem prime_decH_2017843 : Nat.Prime 2017843 := by norm_num
private theorem prime_decH_2049797 : Nat.Prime 2049797 := by norm_num
private theorem prime_decH_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_decH_2098079 : Nat.Prime 2098079 := by norm_num
private theorem prime_decH_2122619 : Nat.Prime 2122619 := by norm_num
private theorem prime_decH_2182451 : Nat.Prime 2182451 := by norm_num
private theorem prime_decH_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_decH_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_decH_2428859 : Nat.Prime 2428859 := by norm_num
private theorem prime_decH_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_decH_2617129 : Nat.Prime 2617129 := by norm_num
private theorem prime_decH_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_decH_3222797 : Nat.Prime 3222797 := by norm_num
private theorem prime_decH_3421567 : Nat.Prime 3421567 := by norm_num
private theorem prime_decH_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_decH_3496469 : Nat.Prime 3496469 := by norm_num
private theorem prime_decH_3509741 : Nat.Prime 3509741 := by norm_num
private theorem prime_decH_3523771 : Nat.Prime 3523771 := by norm_num
private theorem prime_decH_3539743 : Nat.Prime 3539743 := by norm_num
private theorem prime_decH_3586771 : Nat.Prime 3586771 := by norm_num
private theorem prime_decH_3976403 : Nat.Prime 3976403 := by norm_num
private theorem prime_decH_4244609 : Nat.Prime 4244609 := by norm_num
private theorem prime_decH_4673989 : Nat.Prime 4673989 := by norm_num
private theorem prime_decH_4776769 : Nat.Prime 4776769 := by norm_num
private theorem prime_decH_4911391 : Nat.Prime 4911391 := by norm_num
private theorem prime_decH_5026759 : Nat.Prime 5026759 := by norm_num
private theorem prime_decH_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_decH_5075167 : Nat.Prime 5075167 := by norm_num
private theorem prime_decH_5265209 : Nat.Prime 5265209 := by norm_num
private theorem prime_decH_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_decH_6100169 : Nat.Prime 6100169 := by norm_num
private theorem prime_decH_6469943 : Nat.Prime 6469943 := by norm_num
private theorem prime_decH_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_decH_7294097 : Nat.Prime 7294097 := by norm_num
private theorem prime_decH_7482733 : Nat.Prime 7482733 := by norm_num
private theorem prime_decH_7647103 : Nat.Prime 7647103 := by norm_num
private theorem prime_decH_8001839 : Nat.Prime 8001839 := by norm_num
private theorem prime_decH_8092963 : Nat.Prime 8092963 := by norm_num
private theorem prime_decH_9427111 : Nat.Prime 9427111 := by norm_num
private theorem prime_decH_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_decH_9711041 : Nat.Prime 9711041 := by norm_num
private theorem prime_decH_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_decH_9985559 : Nat.Prime 9985559 := by norm_num
private theorem prime_decH_10105057 : Nat.Prime 10105057 := by norm_num
private theorem prime_decH_10379587 : Nat.Prime 10379587 := by norm_num
private theorem prime_decH_11060821 : Nat.Prime 11060821 := by norm_num
private theorem prime_decH_11541421 : Nat.Prime 11541421 := by norm_num
private theorem prime_decH_11637001 : Nat.Prime 11637001 := by norm_num
private theorem prime_decH_13476283 : Nat.Prime 13476283 := by norm_num
private theorem prime_decH_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_decH_14598539 : Nat.Prime 14598539 := by norm_num
private theorem prime_decH_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_decH_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_decH_14889587 : Nat.Prime 14889587 := by norm_num
private theorem prime_decH_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_decH_20271367 : Nat.Prime 20271367 := by norm_num
private theorem prime_decH_20323781 : Nat.Prime 20323781 := by norm_num
private theorem prime_decH_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_decH_21346979 : Nat.Prime 21346979 := by norm_num
private theorem prime_decH_21850733 : Nat.Prime 21850733 := by norm_num
private theorem prime_decH_22852813 : Nat.Prime 22852813 := by norm_num
private theorem prime_decH_23622671 : Nat.Prime 23622671 := by norm_num
private theorem prime_decH_24195499 : Nat.Prime 24195499 := by norm_num
private theorem prime_decH_24555749 : Nat.Prime 24555749 := by norm_num
private theorem prime_decH_24847363 : Nat.Prime 24847363 := by norm_num
private theorem prime_decH_25359827 : Nat.Prime 25359827 := by norm_num
private theorem prime_decH_27212041 : Nat.Prime 27212041 := by norm_num
private theorem prime_decH_29623871 : Nat.Prime 29623871 := by norm_num
private theorem prime_decH_29654903 : Nat.Prime 29654903 := by norm_num

private theorem prime_decH_30126293 : Nat.Prime 30126293 := by
  apply lucas_primality 30126293 (2 : ZMod 30126293)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) = 30126293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_109
      · exact prime_decH_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30126293) ^ 15063146 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 4303756 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 276388 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 3052 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_32364193 : Nat.Prime 32364193 := by
  apply lucas_primality 32364193 (15 : ZMod 32364193)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32364193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_17
      · exact prime_decH_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32364193) ^ 16182096 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 10788064 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 4623456 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 1903776 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 11424 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_983
      · exact prime_decH_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_47684383 : Nat.Prime 47684383 := by
  apply lucas_primality 47684383 (3 : ZMod 47684383)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (233, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (233, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 47684383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_23
      · exact prime_decH_233
      · exact prime_decH_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47684383) ^ 23842191 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 15894794 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 2073234 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 204654 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 32154 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_51803611 : Nat.Prime 51803611 := by
  apply lucas_primality 51803611 (10 : ZMod 51803611)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1726787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1726787, 1)] : List FactorBlock).map factorBlockValue).prod) = 51803611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_1726787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51803611) ^ 25901805 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 17267870 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 10360722 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 30 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_52023863 : Nat.Prime 52023863 := by
  apply lucas_primality 52023863 (5 : ZMod 52023863)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) = 52023863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_19
      · exact prime_decH_124459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52023863) ^ 26011931 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 4729442 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 2738098 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 418 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_52999753 : Nat.Prime 52999753 := by
  apply lucas_primality 52999753 (5 : ZMod 52999753)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (73, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (73, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 52999753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_13
      · exact prime_decH_73
      · exact prime_decH_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52999753) ^ 26499876 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 17666584 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 4076904 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 726024 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 296088 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_56297287 : Nat.Prime 56297287 := by
  apply lucas_primality 56297287 (3 : ZMod 56297287)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) = 56297287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_67
      · exact prime_decH_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56297287) ^ 28148643 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 18765762 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 840258 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 1206 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_56624411 : Nat.Prime 56624411 := by
  apply lucas_primality 56624411 (2 : ZMod 56624411)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) = 56624411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_109
      · exact prime_decH_51949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56624411) ^ 28312205 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 11324882 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 519490 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 1090 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_59247743 : Nat.Prime 59247743 := by
  apply lucas_primality 59247743 (5 : ZMod 59247743)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod) = 59247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_29623871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59247743) ^ 29623871 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 59247743) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_64144099 : Nat.Prime 64144099 := by
  apply lucas_primality 64144099 (2 : ZMod 64144099)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 64144099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_53
      · exact prime_decH_71
      · exact prime_decH_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64144099) ^ 32072049 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 21381366 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 1210266 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 903438 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 67734 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_72659089 : Nat.Prime 72659089 := by
  apply lucas_primality 72659089 (7 : ZMod 72659089)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (67, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (67, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 72659089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_67
      · exact prime_decH_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 72659089) ^ 36329544 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 24219696 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 4274064 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 1084464 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 164016 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_74906501 : Nat.Prime 74906501 := by
  apply lucas_primality 74906501 (2 : ZMod 74906501)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (37, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (37, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 74906501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_37
      · exact prime_decH_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74906501) ^ 37453250 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 74906501) ^ 14981300 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 74906501) ^ 2024500 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 74906501) ^ 18500 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_81085469 : Nat.Prime 81085469 := by
  apply lucas_primality 81085469 (2 : ZMod 81085469)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20271367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20271367, 1)] : List FactorBlock).map factorBlockValue).prod) = 81085469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_20271367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 81085469) ^ 40542734 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 81085469) ^ 4 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_88077317 : Nat.Prime 88077317 := by
  apply lucas_primality 88077317 (2 : ZMod 88077317)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (595117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (595117, 1)] : List FactorBlock).map factorBlockValue).prod) = 88077317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_37
      · exact prime_decH_595117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 88077317) ^ 44038658 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 88077317) ^ 2380468 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 88077317) ^ 148 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_88478713 : Nat.Prime 88478713 := by
  apply lucas_primality 88478713 (13 : ZMod 88478713)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (31, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (31, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 88478713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_31
      · exact prime_decH_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 88478713) ^ 44239356 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 88478713) ^ 29492904 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 88478713) ^ 12639816 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 88478713) ^ 2854152 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 88478713) ^ 109368 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_23
      · exact prime_decH_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_98185877 : Nat.Prime 98185877 := by
  apply lucas_primality 98185877 (2 : ZMod 98185877)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (336253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (336253, 1)] : List FactorBlock).map factorBlockValue).prod) = 98185877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_73
      · exact prime_decH_336253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98185877) ^ 49092938 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98185877) ^ 1345012 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98185877) ^ 292 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_19
      · exact prime_decH_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_107453117 : Nat.Prime 107453117 := by
  apply lucas_primality 107453117 (2 : ZMod 107453117)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (193261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (193261, 1)] : List FactorBlock).map factorBlockValue).prod) = 107453117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_139
      · exact prime_decH_193261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107453117) ^ 53726558 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 107453117) ^ 773044 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 107453117) ^ 556 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_108608761 : Nat.Prime 108608761 := by
  apply lucas_primality 108608761 (34 : ZMod 108608761)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13, 1), (23, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13, 1), (23, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 108608761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_13
      · exact prime_decH_23
      · exact prime_decH_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 108608761) ^ 54304380 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 36202920 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 21721752 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 8354520 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 4722120 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 107640 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_110782159 : Nat.Prime 110782159 := by
  apply lucas_primality 110782159 (3 : ZMod 110782159)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) = 110782159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_31
      · exact prime_decH_19213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110782159) ^ 55391079 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 36927386 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 3573618 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 5766 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_13
      · exact prime_decH_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_135170359 : Nat.Prime 135170359 := by
  apply lucas_primality 135170359 (6 : ZMod 135170359)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135170359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_41
      · exact prime_decH_163
      · exact prime_decH_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135170359) ^ 67585179 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 45056786 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 3296838 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 829266 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 40098 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_137653927 : Nat.Prime 137653927 := by
  apply lucas_primality 137653927 (3 : ZMod 137653927)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) = 137653927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_4013
      · exact prime_decH_5717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137653927) ^ 68826963 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 45884642 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 34302 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 24078 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_149813003 : Nat.Prime 149813003 := by
  apply lucas_primality 149813003 (2 : ZMod 149813003)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (74906501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (74906501, 1)] : List FactorBlock).map factorBlockValue).prod) = 149813003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_74906501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 149813003) ^ 74906501 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149813003) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_163646341 : Nat.Prime 163646341 := by
  apply lucas_primality 163646341 (7 : ZMod 163646341)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) = 163646341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_19073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163646341) ^ 81823170 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 54548780 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 32729268 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 14876940 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 12588180 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 8580 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_167470561 : Nat.Prime 167470561 := by
  apply lucas_primality 167470561 (13 : ZMod 167470561)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 167470561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_19
      · exact prime_decH_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167470561) ^ 83735280 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 55823520 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 33494112 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 8814240 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 27360 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_168607301 : Nat.Prime 168607301 := by
  apply lucas_primality 168607301 (2 : ZMod 168607301)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (43, 1), (113, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (43, 1), (113, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 168607301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_43
      · exact prime_decH_113
      · exact prime_decH_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168607301) ^ 84303650 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 168607301) ^ 33721460 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 168607301) ^ 3921100 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 168607301) ^ 1492100 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 168607301) ^ 485900 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_178045187 : Nat.Prime 178045187 := by
  apply lucas_primality 178045187 (2 : ZMod 178045187)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (8092963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (8092963, 1)] : List FactorBlock).map factorBlockValue).prod) = 178045187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_8092963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178045187) ^ 89022593 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178045187) ^ 16185926 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178045187) ^ 22 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_193301777 : Nat.Prime 193301777 := by
  apply lucas_primality 193301777 (3 : ZMod 193301777)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) = 193301777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_431
      · exact prime_decH_28031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193301777) ^ 96650888 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 448496 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 6896 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_197212943 : Nat.Prime 197212943 := by
  apply lucas_primality 197212943 (5 : ZMod 197212943)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 197212943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_2069
      · exact prime_decH_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 197212943) ^ 98606471 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 95318 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 4138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_225273263 : Nat.Prime 225273263 := by
  apply lucas_primality 225273263 (5 : ZMod 225273263)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) = 225273263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_223
      · exact prime_decH_505097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225273263) ^ 112636631 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 1010194 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 446 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_191
      · exact prime_decH_383
      · exact prime_decH_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_29
      · exact prime_decH_97
      · exact prime_decH_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_282045737 : Nat.Prime 282045737 := by
  apply lucas_primality 282045737 (3 : ZMod 282045737)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 282045737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_97
      · exact prime_decH_137
      · exact prime_decH_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 282045737) ^ 141022868 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 40292248 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2907688 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2058728 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 744184 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_299626007 : Nat.Prime 299626007 := by
  apply lucas_primality 299626007 (5 : ZMod 299626007)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149813003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149813003, 1)] : List FactorBlock).map factorBlockValue).prod) = 299626007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_149813003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 299626007) ^ 149813003 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 299626007) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_359147963 : Nat.Prime 359147963 := by
  apply lucas_primality 359147963 (2 : ZMod 359147963)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod) = 359147963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_47
      · exact prime_decH_71
      · exact prime_decH_53813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 359147963) ^ 179573981 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 7641446 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 5058422 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 6674 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_381624127 : Nat.Prime 381624127 := by
  apply lucas_primality 381624127 (3 : ZMod 381624127)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) = 381624127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_287801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 381624127) ^ 190812063 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 127208042 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 29355702 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 22448478 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 1326 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_417616597 : Nat.Prime 417616597 := by
  apply lucas_primality 417616597 (2 : ZMod 417616597)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1549, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1549, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) = 417616597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_1549
      · exact prime_decH_7489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 417616597) ^ 208808298 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 139205532 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 269604 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 55764 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_426097523 : Nat.Prime 426097523 := by
  apply lucas_primality 426097523 (2 : ZMod 426097523)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) = 426097523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_29
      · exact prime_decH_1117
      · exact prime_decH_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 426097523) ^ 213048761 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 14693018 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 381466 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 64786 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_17
      · exact prime_decH_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_518323783 : Nat.Prime 518323783 := by
  apply lucas_primality 518323783 (5 : ZMod 518323783)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod) = 518323783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_31
      · exact prime_decH_53
      · exact prime_decH_52579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 518323783) ^ 259161891 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 172774594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 16720122 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9779694 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_522823519 : Nat.Prime 522823519 := by
  apply lucas_primality 522823519 (6 : ZMod 522823519)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) = 522823519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_73
      · exact prime_decH_18947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522823519) ^ 261411759 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 174274506 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 74689074 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 7161966 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 27594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_526547381 : Nat.Prime 526547381 := by
  apply lucas_primality 526547381 (3 : ZMod 526547381)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 526547381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_19
      · exact prime_decH_233
      · exact prime_decH_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 526547381) ^ 263273690 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 105309476 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 27713020 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 2259860 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 1682260 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_627237883 : Nat.Prime 627237883 := by
  apply lucas_primality 627237883 (5 : ZMod 627237883)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (2049797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (2049797, 1)] : List FactorBlock).map factorBlockValue).prod) = 627237883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_2049797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 627237883) ^ 313618941 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 627237883) ^ 209079294 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 627237883) ^ 36896346 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 627237883) ^ 306 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_659006597 : Nat.Prime 659006597 := by
  apply lucas_primality 659006597 (2 : ZMod 659006597)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) = 659006597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_257
      · exact prime_decH_641057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 659006597) ^ 329503298 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 2564228 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 1028 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_889647091 : Nat.Prime 889647091 := by
  apply lucas_primality 889647091 (3 : ZMod 889647091)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) = 889647091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_29654903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 889647091) ^ 444823545 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 296549030 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 177929418 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 30 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_894938237 : Nat.Prime 894938237 := by
  apply lucas_primality 894938237 (2 : ZMod 894938237)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod) = 894938237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_2777
      · exact prime_decH_80567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 894938237) ^ 447469118 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 322268 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 11108 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1015645049 : Nat.Prime 1015645049 := by
  apply lucas_primality 1015645049 (3 : ZMod 1015645049)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (11541421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (11541421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015645049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_11541421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1015645049) ^ 507822524 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1015645049) ^ 92331368 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1015645049) ^ 88 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1080452957 : Nat.Prime 1080452957 := by
  apply lucas_primality 1080452957 (2 : ZMod 1080452957)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (24555749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (24555749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080452957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_24555749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1080452957) ^ 540226478 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1080452957) ^ 98222996 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1080452957) ^ 44 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1087747789 : Nat.Prime 1087747789 := by
  apply lucas_primality 1087747789 (2 : ZMod 1087747789)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1087747789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_401
      · exact prime_decH_13297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1087747789) ^ 543873894 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 362582596 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 63985164 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 2712588 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 81804 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1130858507 : Nat.Prime 1130858507 := by
  apply lucas_primality 1130858507 (2 : ZMod 1130858507)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5059, 1), (111767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5059, 1), (111767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130858507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5059
      · exact prime_decH_111767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1130858507) ^ 565429253 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130858507) ^ 223534 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130858507) ^ 10118 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1169428727 : Nat.Prime 1169428727 := by
  apply lucas_primality 1169428727 (5 : ZMod 1169428727)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22811, 1), (25633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22811, 1), (25633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1169428727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_22811
      · exact prime_decH_25633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1169428727) ^ 584714363 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1169428727) ^ 51266 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1169428727) ^ 45622 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1188346277 : Nat.Prime 1188346277 := by
  apply lucas_primality 1188346277 (2 : ZMod 1188346277)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (22852813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (22852813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188346277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_22852813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1188346277) ^ 594173138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188346277) ^ 91411252 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188346277) ^ 52 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_29
      · exact prime_decH_113
      · exact prime_decH_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1223641049 : Nat.Prime 1223641049 := by
  apply lucas_primality 1223641049 (3 : ZMod 1223641049)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (21850733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (21850733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1223641049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_21850733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1223641049) ^ 611820524 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223641049) ^ 174805864 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223641049) ^ 56 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1526496509 : Nat.Prime 1526496509 := by
  apply lucas_primality 1526496509 (2 : ZMod 1526496509)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1526496509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_381624127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1526496509) ^ 763248254 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526496509) ^ 4 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_409
      · exact prime_decH_443
      · exact prime_decH_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_89
      · exact prime_decH_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2267800291 : Nat.Prime 2267800291 := by
  apply lucas_primality 2267800291 (26 : ZMod 2267800291)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267800291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_19
      · exact prime_decH_29
      · exact prime_decH_47
      · exact prime_decH_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2267800291) ^ 1133900145 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 755933430 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 453560058 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 323971470 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 119357910 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 78200010 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 48251070 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 16315110 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_61
      · exact prime_decH_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2397008057 : Nat.Prime 2397008057 := by
  apply lucas_primality 2397008057 (3 : ZMod 2397008057)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (299626007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (299626007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397008057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_299626007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2397008057) ^ 1198504028 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397008057) ^ 8 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3159284287 : Nat.Prime 3159284287 := by
  apply lucas_primality 3159284287 (3 : ZMod 3159284287)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (526547381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (526547381, 1)] : List FactorBlock).map factorBlockValue).prod) = 3159284287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_526547381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3159284287) ^ 1579642143 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159284287) ^ 1053094762 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159284287) ^ 6 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3308692097 : Nat.Prime 3308692097 := by
  apply lucas_primality 3308692097 (3 : ZMod 3308692097)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (4007, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (4007, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3308692097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_4007
      · exact prime_decH_6451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3308692097) ^ 1654346048 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3308692097) ^ 825728 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3308692097) ^ 512896 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_4070273261 : Nat.Prime 4070273261 := by
  apply lucas_primality 4070273261 (2 : ZMod 4070273261)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070273261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_97
      · exact prime_decH_2098079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4070273261) ^ 2035136630 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 814054652 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 41961580 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 1940 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5564150981 : Nat.Prime 5564150981 := by
  apply lucas_primality 5564150981 (2 : ZMod 5564150981)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (6469943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (6469943, 1)] : List FactorBlock).map factorBlockValue).prod) = 5564150981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_43
      · exact prime_decH_6469943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5564150981) ^ 2782075490 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5564150981) ^ 1112830196 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5564150981) ^ 129398860 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5564150981) ^ 860 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_7795619827 : Nat.Prime 7795619827 := by
  apply lucas_primality 7795619827 (3 : ZMod 7795619827)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (14598539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (14598539, 1)] : List FactorBlock).map factorBlockValue).prod) = 7795619827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_89
      · exact prime_decH_14598539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7795619827) ^ 3897809913 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 2598539942 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 87591234 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 534 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_8015795369 : Nat.Prime 8015795369 := by
  apply lucas_primality 8015795369 (3 : ZMod 8015795369)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (73, 1), (103, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (73, 1), (103, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod) = 8015795369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_73
      · exact prime_decH_103
      · exact prime_decH_19037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8015795369) ^ 4007897684 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 1145113624 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 109805416 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 77823256 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 421064 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_9003352679 : Nat.Prime 9003352679 := by
  apply lucas_primality 9003352679 (19 : ZMod 9003352679)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1039, 1), (1627, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1039, 1), (1627, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9003352679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_1039
      · exact prime_decH_1627
      · exact prime_decH_2663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 9003352679) ^ 4501676339 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 8665402 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 5533714 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 3380906 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_9278485297 : Nat.Prime 9278485297 := by
  apply lucas_primality 9278485297 (5 : ZMod 9278485297)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9278485297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_193301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9278485297) ^ 4639242648 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 3092828432 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 48 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_10040813917 : Nat.Prime 10040813917 := by
  apply lucas_primality 10040813917 (23 : ZMod 10040813917)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3413, 1), (35023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3413, 1), (35023, 1)] : List FactorBlock).map factorBlockValue).prod) = 10040813917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_3413
      · exact prime_decH_35023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 10040813917) ^ 5020406958 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 3346937972 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 1434401988 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 2941932 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 286692 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_10464329423 : Nat.Prime 10464329423 := by
  apply lucas_primality 10464329423 (5 : ZMod 10464329423)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (51803611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (51803611, 1)] : List FactorBlock).map factorBlockValue).prod) = 10464329423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_101
      · exact prime_decH_51803611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10464329423) ^ 5232164711 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 10464329423) ^ 103607222 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 10464329423) ^ 202 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_10971529141 : Nat.Prime 10971529141 := by
  apply lucas_primality 10971529141 (2 : ZMod 10971529141)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (1278733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (1278733, 1)] : List FactorBlock).map factorBlockValue).prod) = 10971529141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_1278733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10971529141) ^ 5485764570 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 3657176380 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 2194305828 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 997411740 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 843963780 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 8580 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_15383
      · exact prime_decH_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_12103873247 : Nat.Prime 12103873247 := by
  apply lucas_primality 12103873247 (5 : ZMod 12103873247)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (59, 1), (2182451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (59, 1), (2182451, 1)] : List FactorBlock).map factorBlockValue).prod) = 12103873247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_47
      · exact prime_decH_59
      · exact prime_decH_2182451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12103873247) ^ 6051936623 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 257529218 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 205150394 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 5546 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_13426020743 : Nat.Prime 13426020743 := by
  apply lucas_primality 13426020743 (5 : ZMod 13426020743)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (599, 1), (659237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (599, 1), (659237, 1)] : List FactorBlock).map factorBlockValue).prod) = 13426020743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_17
      · exact prime_decH_599
      · exact prime_decH_659237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13426020743) ^ 6713010371 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13426020743) ^ 789765926 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13426020743) ^ 22414058 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13426020743) ^ 20366 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_23
      · exact prime_decH_47
      · exact prime_decH_59
      · exact prime_decH_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_349
      · exact prime_decH_619
      · exact prime_decH_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_15723092741 : Nat.Prime 15723092741 := by
  apply lucas_primality 15723092741 (2 : ZMod 15723092741)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (25359827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (25359827, 1)] : List FactorBlock).map factorBlockValue).prod) = 15723092741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_31
      · exact prime_decH_25359827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15723092741) ^ 7861546370 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 3144618548 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 507196540 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 620 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_17755350889 : Nat.Prime 17755350889 := by
  apply lucas_primality 17755350889 (14 : ZMod 17755350889)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) = 17755350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_11
      · exact prime_decH_19
      · exact prime_decH_3539743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17755350889) ^ 8877675444 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5918450296 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 1614122808 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 934492152 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5016 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_24014736307 : Nat.Prime 24014736307 := by
  apply lucas_primality 24014736307 (3 : ZMod 24014736307)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (13476283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (13476283, 1)] : List FactorBlock).map factorBlockValue).prod) = 24014736307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_11
      · exact prime_decH_13476283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24014736307) ^ 12007368153 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24014736307) ^ 8004912102 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24014736307) ^ 2183157846 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24014736307) ^ 1782 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_24069498209 : Nat.Prime 24069498209 := by
  apply lucas_primality 24069498209 (3 : ZMod 24069498209)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (107453117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (107453117, 1)] : List FactorBlock).map factorBlockValue).prod) = 24069498209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_107453117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24069498209) ^ 12034749104 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24069498209) ^ 3438499744 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24069498209) ^ 224 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_24330664621 : Nat.Prime 24330664621 := by
  apply lucas_primality 24330664621 (2 : ZMod 24330664621)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) = 24330664621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_135170359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24330664621) ^ 12165332310 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 8110221540 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 4866132924 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 180 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_24522826583 : Nat.Prime 24522826583 := by
  apply lucas_primality 24522826583 (5 : ZMod 24522826583)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod) = 24522826583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_577
      · exact prime_decH_685493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24522826583) ^ 12261413291 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 791058922 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 42500566 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 35774 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_71
      · exact prime_decH_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_27665871067 : Nat.Prime 27665871067 := by
  apply lucas_primality 27665871067 (2 : ZMod 27665871067)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (52999753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (52999753, 1)] : List FactorBlock).map factorBlockValue).prod) = 27665871067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_29
      · exact prime_decH_52999753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27665871067) ^ 13832935533 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 9221957022 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 953995554 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 522 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_17
      · exact prime_decH_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_36189016433 : Nat.Prime 36189016433 := by
  apply lucas_primality 36189016433 (3 : ZMod 36189016433)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (9091, 1), (248797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (9091, 1), (248797, 1)] : List FactorBlock).map factorBlockValue).prod) = 36189016433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_9091
      · exact prime_decH_248797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36189016433) ^ 18094508216 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36189016433) ^ 3980752 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36189016433) ^ 145456 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_151
      · exact prime_decH_479
      · exact prime_decH_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_45773802457 : Nat.Prime 45773802457 := by
  apply lucas_primality 45773802457 (5 : ZMod 45773802457)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (191, 1), (9985559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (191, 1), (9985559, 1)] : List FactorBlock).map factorBlockValue).prod) = 45773802457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_191
      · exact prime_decH_9985559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45773802457) ^ 22886901228 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 45773802457) ^ 15257934152 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 45773802457) ^ 239653416 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 45773802457) ^ 4584 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_51033940343 : Nat.Prime 51033940343 := by
  apply lucas_primality 51033940343 (10 : ZMod 51033940343)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) = 51033940343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_30126293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51033940343) ^ 25516970171 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 7290562906 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 4639449122 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 1694 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_68032800707 : Nat.Prime 68032800707 := by
  apply lucas_primality 68032800707 (2 : ZMod 68032800707)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (5623, 1), (9901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (5623, 1), (9901, 1)] : List FactorBlock).map factorBlockValue).prod) = 68032800707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_47
      · exact prime_decH_5623
      · exact prime_decH_9901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68032800707) ^ 34016400353 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 68032800707) ^ 5233292362 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 68032800707) ^ 1447506398 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 68032800707) ^ 12099022 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 68032800707) ^ 6871306 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_71172712477 : Nat.Prime 71172712477 := by
  apply lucas_primality 71172712477 (2 : ZMod 71172712477)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) = 71172712477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_659006597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71172712477) ^ 35586356238 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 23724237492 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 108 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_84575179597 : Nat.Prime 84575179597 := by
  apply lucas_primality 84575179597 (2 : ZMod 84575179597)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (72659089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (72659089, 1)] : List FactorBlock).map factorBlockValue).prod) = 84575179597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_97
      · exact prime_decH_72659089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84575179597) ^ 42287589798 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 28191726532 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 871909068 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 1164 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_90332674877 : Nat.Prime 90332674877 := by
  apply lucas_primality 90332674877 (2 : ZMod 90332674877)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod) = 90332674877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_53
      · exact prime_decH_426097523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90332674877) ^ 45166337438 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 1704390092 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 212 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_98043152197 : Nat.Prime 98043152197 := by
  apply lucas_primality 98043152197 (2 : ZMod 98043152197)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (10099, 1), (73547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (10099, 1), (73547, 1)] : List FactorBlock).map factorBlockValue).prod) = 98043152197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_11
      · exact prime_decH_10099
      · exact prime_decH_73547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98043152197) ^ 49021576098 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 32681050732 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 8913013836 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 9708204 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 1333068 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_102067880687 : Nat.Prime 102067880687 := by
  apply lucas_primality 102067880687 (5 : ZMod 102067880687)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) = 102067880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_51033940343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 102067880687) ^ 51033940343 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 102067880687) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_110719776691 : Nat.Prime 110719776691 := by
  apply lucas_primality 110719776691 (10 : ZMod 110719776691)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (2897, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (2897, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod) = 110719776691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_2897
      · exact prime_decH_141551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 110719776691) ^ 55359888345 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 36906592230 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 22143955338 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 38218770 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 782190 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_121827752369 : Nat.Prime 121827752369 := by
  apply lucas_primality 121827752369 (3 : ZMod 121827752369)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) = 121827752369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_1087747789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 121827752369) ^ 60913876184 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 17403964624 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 112 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_11
      · exact prime_decH_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_161869470179 : Nat.Prime 161869470179 := by
  apply lucas_primality 161869470179 (2 : ZMod 161869470179)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) = 161869470179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_41
      · exact prime_decH_59
      · exact prime_decH_271
      · exact prime_decH_9497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161869470179) ^ 80934735089 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 12451497706 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 3948035858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 2743550342 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 597304318 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 17044274 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_169668913487 : Nat.Prime 169668913487 := by
  apply lucas_primality 169668913487 (5 : ZMod 169668913487)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (751, 1), (4911391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (751, 1), (4911391, 1)] : List FactorBlock).map factorBlockValue).prod) = 169668913487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_23
      · exact prime_decH_751
      · exact prime_decH_4911391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 169668913487) ^ 84834456743 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 169668913487) ^ 7376909282 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 169668913487) ^ 225923986 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 169668913487) ^ 34546 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_219613389623 : Nat.Prime 219613389623 := by
  apply lucas_primality 219613389623 (5 : ZMod 219613389623)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) = 219613389623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_61
      · exact prime_decH_163646341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 219613389623) ^ 109806694811 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 19964853602 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 3600219502 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 1342 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_236131189291 : Nat.Prime 236131189291 := by
  apply lucas_primality 236131189291 (2 : ZMod 236131189291)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (34367, 1), (76343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (34367, 1), (76343, 1)] : List FactorBlock).map factorBlockValue).prod) = 236131189291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_34367
      · exact prime_decH_76343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 236131189291) ^ 118065594645 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 78710396430 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 47226237858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 6870870 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 3093030 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_237841108607 : Nat.Prime 237841108607 := by
  apply lucas_primality 237841108607 (5 : ZMod 237841108607)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) = 237841108607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_1093
      · exact prime_decH_3509741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237841108607) ^ 118920554303 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 7672293826 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 217603942 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 67766 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_400062744481 : Nat.Prime 400062744481 := by
  apply lucas_primality 400062744481 (23 : ZMod 400062744481)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod) = 400062744481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_19
      · exact prime_decH_131
      · exact prime_decH_47837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 400062744481) ^ 200031372240 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 133354248160 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 80012548896 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 57151820640 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 21055933920 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 3053914080 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 8363040 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_417309099223 : Nat.Prime 417309099223 := by
  apply lucas_primality 417309099223 (3 : ZMod 417309099223)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (3793, 1), (52541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (3793, 1), (52541, 1)] : List FactorBlock).map factorBlockValue).prod) = 417309099223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_349
      · exact prime_decH_3793
      · exact prime_decH_52541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 417309099223) ^ 208654549611 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 139103033074 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 1195728078 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 110020854 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 7942542 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_17
      · exact prime_decH_397
      · exact prime_decH_2531
      · exact prime_decH_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_587043060839 : Nat.Prime 587043060839 := by
  apply lucas_primality 587043060839 (7 : ZMod 587043060839)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (1188346277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (1188346277, 1)] : List FactorBlock).map factorBlockValue).prod) = 587043060839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_19
      · exact prime_decH_1188346277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 587043060839) ^ 293521530419 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 45157158526 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 30897003202 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 494 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_29
      · exact prime_decH_34361
      · exact prime_decH_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod) = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_739
      · exact prime_decH_1307
      · exact prime_decH_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_800290856627 : Nat.Prime 800290856627 := by
  apply lucas_primality 800290856627 (2 : ZMod 800290856627)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (71, 1), (103, 1), (1334561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (71, 1), (103, 1), (1334561, 1)] : List FactorBlock).map factorBlockValue).prod) = 800290856627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_41
      · exact prime_decH_71
      · exact prime_decH_103
      · exact prime_decH_1334561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 800290856627) ^ 400145428313 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 800290856627) ^ 19519289186 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 800290856627) ^ 11271702206 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 800290856627) ^ 7769814142 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 800290856627) ^ 599666 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_955333581581 : Nat.Prime 955333581581 := by
  apply lucas_primality 955333581581 (10 : ZMod 955333581581)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod) = 955333581581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_19
      · exact prime_decH_359147963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 955333581581) ^ 477666790790 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 191066716316 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 136476225940 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 50280714820 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 2660 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1062244745567 : Nat.Prime 1062244745567 := by
  apply lucas_primality 1062244745567 (5 : ZMod 1062244745567)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (6221, 1), (301681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (6221, 1), (301681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1062244745567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_283
      · exact prime_decH_6221
      · exact prime_decH_301681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1062244745567) ^ 531122372783 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1062244745567) ^ 3753515002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1062244745567) ^ 170751446 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1062244745567) ^ 3521086 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1342324511921 : Nat.Prime 1342324511921 := by
  apply lucas_primality 1342324511921 (3 : ZMod 1342324511921)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (2397008057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (2397008057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342324511921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_2397008057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1342324511921) ^ 671162255960 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1342324511921) ^ 268464902384 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1342324511921) ^ 191760644560 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1342324511921) ^ 560 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1372447766351 : Nat.Prime 1372447766351 := by
  apply lucas_primality 1372447766351 (7 : ZMod 1372447766351)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1372447766351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_17
      · exact prime_decH_9473
      · exact prime_decH_170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1372447766351) ^ 686223883175 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 274489553270 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 80732221550 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 144879950 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 8052050 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_397
      · exact prime_decH_977
      · exact prime_decH_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1483112670203 : Nat.Prime 1483112670203 := by
  apply lucas_primality 1483112670203 (2 : ZMod 1483112670203)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483112670203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_23
      · exact prime_decH_30871
      · exact prime_decH_1044397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483112670203) ^ 741556335101 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 64483159574 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 48042262 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 1420066 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_35279
      · exact prime_decH_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1529752406099 : Nat.Prime 1529752406099 := by
  apply lucas_primality 1529752406099 (2 : ZMod 1529752406099)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1529752406099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_47
      · exact prime_decH_89
      · exact prime_decH_617
      · exact prime_decH_42337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1529752406099) ^ 764876203049 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 218536058014 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 32547923534 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 17188229282 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 2479339394 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 36132754 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1853410441097 : Nat.Prime 1853410441097 := by
  apply lucas_primality 1853410441097 (3 : ZMod 1853410441097)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23857, 1), (9711041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23857, 1), (9711041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1853410441097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_23857
      · exact prime_decH_9711041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1853410441097) ^ 926705220548 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1853410441097) ^ 77688328 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1853410441097) ^ 190856 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1981109685367 : Nat.Prime 1981109685367 := by
  apply lucas_primality 1981109685367 (3 : ZMod 1981109685367)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (15723092741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (15723092741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1981109685367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_15723092741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1981109685367) ^ 990554842683 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 660369895122 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 283015669338 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 126 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2231902209599 : Nat.Prime 2231902209599 := by
  apply lucas_primality 2231902209599 (19 : ZMod 2231902209599)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2231902209599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_2153
      · exact prime_decH_518323783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 2231902209599) ^ 1115951104799 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 1036647566 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 4306 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2729747741957 : Nat.Prime 2729747741957 := by
  apply lucas_primality 2729747741957 (2 : ZMod 2729747741957)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (241, 1), (2053, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (241, 1), (2053, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729747741957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_149
      · exact prime_decH_241
      · exact prime_decH_2053
      · exact prime_decH_9257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2729747741957) ^ 1364873870978 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 18320454644 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 11326754116 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 1329638452 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 294884708 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_761
      · exact prime_decH_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_4411391750663 : Nat.Prime 4411391750663 := by
  apply lucas_primality 4411391750663 (5 : ZMod 4411391750663)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (169668913487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (169668913487, 1)] : List FactorBlock).map factorBlockValue).prod) = 4411391750663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_169668913487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4411391750663) ^ 2205695875331 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4411391750663) ^ 339337826974 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4411391750663) ^ 26 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_4887540332063 : Nat.Prime 4887540332063 := by
  apply lucas_primality 4887540332063 (5 : ZMod 4887540332063)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod) = 4887540332063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_41
      · exact prime_decH_433
      · exact prime_decH_137653927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4887540332063) ^ 2443770166031 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 119208300782 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 11287622014 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 35506 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_381559
      · exact prime_decH_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5134675637989 : Nat.Prime 5134675637989 := by
  apply lucas_primality 5134675637989 (2 : ZMod 5134675637989)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (10971529141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (10971529141, 1)] : List FactorBlock).map factorBlockValue).prod) = 5134675637989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_13
      · exact prime_decH_10971529141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5134675637989) ^ 2567337818994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 1711558545996 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 394975049076 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 468 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5686502827427 : Nat.Prime 5686502827427 := by
  apply lucas_primality 5686502827427 (2 : ZMod 5686502827427)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (98043152197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (98043152197, 1)] : List FactorBlock).map factorBlockValue).prod) = 5686502827427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_29
      · exact prime_decH_98043152197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5686502827427) ^ 2843251413713 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5686502827427) ^ 196086304394 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5686502827427) ^ 58 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5742406021717 : Nat.Prime 5742406021717 := by
  apply lucas_primality 5742406021717 (2 : ZMod 5742406021717)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (13, 1), (601, 1), (972197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (13, 1), (601, 1), (972197, 1)] : List FactorBlock).map factorBlockValue).prod) = 5742406021717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_13
      · exact prime_decH_601
      · exact prime_decH_972197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5742406021717) ^ 2871203010858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742406021717) ^ 1914135340572 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742406021717) ^ 820343717388 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742406021717) ^ 441723540132 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742406021717) ^ 9554752116 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742406021717) ^ 5906628 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_6373468473403 : Nat.Prime 6373468473403 := by
  apply lucas_primality 6373468473403 (2 : ZMod 6373468473403)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1062244745567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1062244745567, 1)] : List FactorBlock).map factorBlockValue).prod) = 6373468473403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_1062244745567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6373468473403) ^ 3186734236701 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373468473403) ^ 2124489491134 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373468473403) ^ 6 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_7924438741469 : Nat.Prime 7924438741469 := by
  apply lucas_primality 7924438741469 (2 : ZMod 7924438741469)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1981109685367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1981109685367, 1)] : List FactorBlock).map factorBlockValue).prod) = 7924438741469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_1981109685367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7924438741469) ^ 3962219370734 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7924438741469) ^ 4 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_8155122571867 : Nat.Prime 8155122571867 := by
  apply lucas_primality 8155122571867 (2 : ZMod 8155122571867)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (127, 1), (98185877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (127, 1), (98185877, 1)] : List FactorBlock).map factorBlockValue).prod) = 8155122571867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_109
      · exact prime_decH_127
      · exact prime_decH_98185877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8155122571867) ^ 4077561285933 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8155122571867) ^ 2718374190622 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8155122571867) ^ 74817638274 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8155122571867) ^ 64213563558 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8155122571867) ^ 83058 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_13
      · exact prime_decH_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_22575350790673 : Nat.Prime 22575350790673 := by
  apply lucas_primality 22575350790673 (10 : ZMod 22575350790673)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (27665871067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (27665871067, 1)] : List FactorBlock).map factorBlockValue).prod) = 22575350790673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_27665871067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 22575350790673) ^ 11287675395336 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 7525116930224 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 1327961811216 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 816 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_23967228153311 : Nat.Prime 23967228153311 := by
  apply lucas_primality 23967228153311 (7 : ZMod 23967228153311)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (8015795369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (8015795369, 1)] : List FactorBlock).map factorBlockValue).prod) = 23967228153311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_13
      · exact prime_decH_23
      · exact prime_decH_8015795369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23967228153311) ^ 11983614076655 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 4793445630662 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 1843632934870 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 1042053397970 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 2990 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_25493873893613 : Nat.Prime 25493873893613 := by
  apply lucas_primality 25493873893613 (2 : ZMod 25493873893613)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6373468473403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6373468473403, 1)] : List FactorBlock).map factorBlockValue).prod) = 25493873893613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_6373468473403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25493873893613) ^ 12746936946806 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 25493873893613) ^ 4 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_26468350503979 : Nat.Prime 26468350503979 := by
  apply lucas_primality 26468350503979 (2 : ZMod 26468350503979)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4411391750663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4411391750663, 1)] : List FactorBlock).map factorBlockValue).prod) = 26468350503979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_4411391750663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26468350503979) ^ 13234175251989 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26468350503979) ^ 8822783501326 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26468350503979) ^ 6 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_23
      · exact prime_decH_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_37214467928927 : Nat.Prime 37214467928927 := by
  apply lucas_primality 37214467928927 (5 : ZMod 37214467928927)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod) = 37214467928927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_41
      · exact prime_decH_18757
      · exact prime_decH_24195499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37214467928927) ^ 18607233964463 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 907669949486 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1984030918 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1538074 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_42038753447953 : Nat.Prime 42038753447953 := by
  apply lucas_primality 42038753447953 (7 : ZMod 42038753447953)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (47857, 1), (6100169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (47857, 1), (6100169, 1)] : List FactorBlock).map factorBlockValue).prod) = 42038753447953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_47857
      · exact prime_decH_6100169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42038753447953) ^ 21019376723976 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 14012917815984 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 878424336 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 6891408 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_47934456306623 : Nat.Prime 47934456306623 := by
  apply lucas_primality 47934456306623 (5 : ZMod 47934456306623)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23967228153311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23967228153311, 1)] : List FactorBlock).map factorBlockValue).prod) = 47934456306623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_23967228153311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 47934456306623) ^ 23967228153311 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 47934456306623) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_56191230356363 : Nat.Prime 56191230356363 := by
  apply lucas_primality 56191230356363 (2 : ZMod 56191230356363)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (73, 1), (653, 1), (20323781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (73, 1), (653, 1), (20323781, 1)] : List FactorBlock).map factorBlockValue).prod) = 56191230356363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_29
      · exact prime_decH_73
      · exact prime_decH_653
      · exact prime_decH_20323781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56191230356363) ^ 28095615178181 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 1937628632978 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 769742881594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 86050888754 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 2764802 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_92149960118093 : Nat.Prime 92149960118093 := by
  apply lucas_primality 92149960118093 (2 : ZMod 92149960118093)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (281, 1), (1223641049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (281, 1), (1223641049, 1)] : List FactorBlock).map factorBlockValue).prod) = 92149960118093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_67
      · exact prime_decH_281
      · exact prime_decH_1223641049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92149960118093) ^ 46074980059046 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 1375372539076 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 327935801132 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 75308 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_95868912613247 : Nat.Prime 95868912613247 := by
  apply lucas_primality 95868912613247 (5 : ZMod 95868912613247)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47934456306623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47934456306623, 1)] : List FactorBlock).map factorBlockValue).prod) = 95868912613247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_47934456306623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 95868912613247) ^ 47934456306623 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 95868912613247) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_158796207522221 : Nat.Prime 158796207522221 := by
  apply lucas_primality 158796207522221 (2 : ZMod 158796207522221)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) = 158796207522221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_17
      · exact prime_decH_14431
      · exact prime_decH_32364193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158796207522221) ^ 79398103761110 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 31759241504444 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 9340953383660 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 11003825620 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 4906540 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_1163
      · exact prime_decH_1663
      · exact prime_decH_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_296123742126743 : Nat.Prime 296123742126743 := by
  apply lucas_primality 296123742126743 (5 : ZMod 296123742126743)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) = 296123742126743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_269
      · exact prime_decH_17755350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296123742126743) ^ 148061871063371 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 9552378778282 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 1100831755118 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 16678 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_378208505146807 : Nat.Prime 378208505146807 := by
  apply lucas_primality 378208505146807 (3 : ZMod 378208505146807)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (199, 1), (117877, 1), (895729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (199, 1), (117877, 1), (895729, 1)] : List FactorBlock).map factorBlockValue).prod) = 378208505146807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_199
      · exact prime_decH_117877
      · exact prime_decH_895729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 378208505146807) ^ 189104252573403 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 378208505146807) ^ 126069501715602 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 378208505146807) ^ 1900545251994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 378208505146807) ^ 3208501278 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 378208505146807) ^ 422235414 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_386519565736481 : Nat.Prime 386519565736481 := by
  apply lucas_primality 386519565736481 (3 : ZMod 386519565736481)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) = 386519565736481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_11
      · exact prime_decH_219613389623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 386519565736481) ^ 193259782868240 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 77303913147296 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 35138142339680 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 1760 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_388383853927687 : Nat.Prime 388383853927687 := by
  apply lucas_primality 388383853927687 (3 : ZMod 388383853927687)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (363563, 1), (178045187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (363563, 1), (178045187, 1)] : List FactorBlock).map factorBlockValue).prod) = 388383853927687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_363563
      · exact prime_decH_178045187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 388383853927687) ^ 194191926963843 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 129461284642562 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 1068271122 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 2181378 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_67
      · exact prime_decH_28807
      · exact prime_decH_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_493853323129583 : Nat.Prime 493853323129583 := by
  apply lucas_primality 493853323129583 (5 : ZMod 493853323129583)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3976403, 1), (4776769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3976403, 1), (4776769, 1)] : List FactorBlock).map factorBlockValue).prod) = 493853323129583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_3976403
      · exact prime_decH_4776769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 493853323129583) ^ 246926661564791 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 37988717163814 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 124195994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 103386478 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_518378746886659 : Nat.Prime 518378746886659 := by
  apply lucas_primality 518378746886659 (3 : ZMod 518378746886659)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (12379, 1), (110782159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (12379, 1), (110782159, 1)] : List FactorBlock).map factorBlockValue).prod) = 518378746886659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_12379
      · exact prime_decH_110782159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 518378746886659) ^ 259189373443329 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 172792915628886 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 74054106698094 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 41875656102 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 4679262 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_576001613200633 : Nat.Prime 576001613200633 := by
  apply lucas_primality 576001613200633 (5 : ZMod 576001613200633)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) = 576001613200633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_197
      · exact prime_decH_121827752369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 576001613200633) ^ 288000806600316 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 192000537733544 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 2923866056856 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 4728 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_1123
      · exact prime_decH_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_47
      · exact prime_decH_71
      · exact prime_decH_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1046224465078031 : Nat.Prime 1046224465078031 := by
  apply lucas_primality 1046224465078031 (7 : ZMod 1046224465078031)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (59, 1), (36189016433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (59, 1), (36189016433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1046224465078031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_59
      · exact prime_decH_36189016433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1046224465078031) ^ 523112232539015 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046224465078031) ^ 209244893015606 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046224465078031) ^ 149460637868290 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046224465078031) ^ 17732618052170 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046224465078031) ^ 28910 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1463629363053257 : Nat.Prime 1463629363053257 := by
  apply lucas_primality 1463629363053257 (3 : ZMod 1463629363053257)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (137, 1), (10040813917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (137, 1), (10040813917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1463629363053257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_19
      · exact prime_decH_137
      · exact prime_decH_10040813917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1463629363053257) ^ 731814681526628 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 209089909007608 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 77033124371224 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 10683426007688 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 145768 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1472991480313183 : Nat.Prime 1472991480313183 := by
  apply lucas_primality 1472991480313183 (5 : ZMod 1472991480313183)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472991480313183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_156521
      · exact prime_decH_522823519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1472991480313183) ^ 736495740156591 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 490997160104394 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 9410823342 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 2817378 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1515807687150209 : Nat.Prime 1515807687150209 := by
  apply lucas_primality 1515807687150209 (3 : ZMod 1515807687150209)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (37, 1), (68477, 1), (4673989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (37, 1), (68477, 1), (4673989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1515807687150209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_37
      · exact prime_decH_68477
      · exact prime_decH_4673989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1515807687150209) ^ 757903843575104 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1515807687150209) ^ 40967775328384 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1515807687150209) ^ 22136011904 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1515807687150209) ^ 324307072 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11
      · exact prime_decH_41
      · exact prime_decH_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1919431841927447 : Nat.Prime 1919431841927447 := by
  apply lucas_primality 1919431841927447 (5 : ZMod 1919431841927447)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (3767, 1), (3308692097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (3767, 1), (3308692097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1919431841927447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_3767
      · exact prime_decH_3308692097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1919431841927447) ^ 959715920963723 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919431841927447) ^ 274204548846778 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919431841927447) ^ 174493803811586 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919431841927447) ^ 509538582938 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919431841927447) ^ 580118 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2232352902117203 : Nat.Prime 2232352902117203 := by
  apply lucas_primality 2232352902117203 (2 : ZMod 2232352902117203)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (3109, 1), (1169428727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (3109, 1), (1169428727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2232352902117203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_307
      · exact prime_decH_3109
      · exact prime_decH_1169428727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2232352902117203) ^ 1116176451058601 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2232352902117203) ^ 7271507824486 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2232352902117203) ^ 718029238378 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2232352902117203) ^ 1908926 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2743295750628703 : Nat.Prime 2743295750628703 := by
  apply lucas_primality 2743295750628703 (5 : ZMod 2743295750628703)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2743295750628703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_2531
      · exact prime_decH_3049
      · exact prime_decH_59247743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2743295750628703) ^ 1371647875314351 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 914431916876234 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 1083878210442 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 899736225198 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 46302114 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2820880298726107 : Nat.Prime 2820880298726107 := by
  apply lucas_primality 2820880298726107 (3 : ZMod 2820880298726107)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820880298726107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_317
      · exact prime_decH_1483112670203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2820880298726107) ^ 1410440149363053 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 940293432908702 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 8898676021218 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 1902 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3008297016953401 : Nat.Prime 3008297016953401 := by
  apply lucas_primality 3008297016953401 (17 : ZMod 3008297016953401)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (659, 1), (733, 1), (10379587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (659, 1), (733, 1), (10379587, 1)] : List FactorBlock).map factorBlockValue).prod) = 3008297016953401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_659
      · exact prime_decH_733
      · exact prime_decH_10379587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3008297016953401) ^ 1504148508476700 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 1002765672317800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 601659403390680 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 4564942362600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 4104088699800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 289828200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5523140549247743 : Nat.Prime 5523140549247743 := by
  apply lucas_primality 5523140549247743 (5 : ZMod 5523140549247743)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523140549247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_101
      · exact prime_decH_463
      · exact prime_decH_631
      · exact prime_decH_97387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5523140549247743) ^ 2761570274623871 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 178165824169282 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 54684559893542 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 11929029264034 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 8752996116082 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 56713324666 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_9271321778674247 : Nat.Prime 9271321778674247 := by
  apply lucas_primality 9271321778674247 (5 : ZMod 9271321778674247)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9271321778674247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_31
      · exact prime_decH_67
      · exact prime_decH_2231902209599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9271321778674247) ^ 4635660889337123 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 299074896086266 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 138377936995138 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 4154 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_9435262352856497 : Nat.Prime 9435262352856497 := by
  apply lucas_primality 9435262352856497 (3 : ZMod 9435262352856497)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (991, 1), (45773802457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (991, 1), (45773802457, 1)] : List FactorBlock).map factorBlockValue).prod) = 9435262352856497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_991
      · exact prime_decH_45773802457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9435262352856497) ^ 4717631176428248 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435262352856497) ^ 725789411758192 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435262352856497) ^ 9520950911056 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435262352856497) ^ 206128 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_10950386820164879 : Nat.Prime 10950386820164879 := by
  apply lucas_primality 10950386820164879 (17 : ZMod 10950386820164879)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) = 10950386820164879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3586771
      · exact prime_decH_1526496509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 10950386820164879) ^ 5475193410082439 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 3052993018 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 7173542 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_67
      · exact prime_decH_97
      · exact prime_decH_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_13528531400913343 : Nat.Prime 13528531400913343 := by
  apply lucas_primality 13528531400913343 (3 : ZMod 13528531400913343)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (631, 1), (10243, 1), (3523771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (631, 1), (10243, 1), (3523771, 1)] : List FactorBlock).map factorBlockValue).prod) = 13528531400913343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_11
      · exact prime_decH_631
      · exact prime_decH_10243
      · exact prime_decH_3523771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13528531400913343) ^ 6764265700456671 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 4509510466971114 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 1229866490992122 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 21439827893682 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 1320758703594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 3839219802 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_14484700483141487 : Nat.Prime 14484700483141487 := by
  apply lucas_primality 14484700483141487 (5 : ZMod 14484700483141487)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (73, 1), (587043060839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (73, 1), (587043060839, 1)] : List FactorBlock).map factorBlockValue).prod) = 14484700483141487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13
      · exact prime_decH_73
      · exact prime_decH_587043060839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14484700483141487) ^ 7242350241570743 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 1114207729472422 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 198420554563582 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 24674 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_14895713529653239 : Nat.Prime 14895713529653239 := by
  apply lucas_primality 14895713529653239 (6 : ZMod 14895713529653239)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61637, 1), (13426020743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61637, 1), (13426020743, 1)] : List FactorBlock).map factorBlockValue).prod) = 14895713529653239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_61637
      · exact prime_decH_13426020743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14895713529653239) ^ 7447856764826619 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 14895713529653239) ^ 4965237843217746 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 14895713529653239) ^ 241668373374 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (6 : ZMod 14895713529653239) ^ 1109466 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_19
      · exact prime_decH_656951
      · exact prime_decH_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_28583317353999781 : Nat.Prime 28583317353999781 := by
  apply lucas_primality 28583317353999781 (2 : ZMod 28583317353999781)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) = 28583317353999781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_158796207522221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28583317353999781) ^ 14291658676999890 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 9527772451333260 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 5716663470799956 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 180 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_33479182882496993 : Nat.Prime 33479182882496993 := by
  apply lucas_primality 33479182882496993 (3 : ZMod 33479182882496993)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1046224465078031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1046224465078031, 1)] : List FactorBlock).map factorBlockValue).prod) = 33479182882496993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_1046224465078031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 33479182882496993) ^ 16739591441248496 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 33479182882496993) ^ 32 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_33531643827487633 : Nat.Prime 33531643827487633 := by
  apply lucas_primality 33531643827487633 (15 : ZMod 33531643827487633)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) = 33531643827487633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_509
      · exact prime_decH_1372447766351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 33531643827487633) ^ 16765821913743816 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 11177214609162544 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 65877492784848 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 24432 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_34129332890315933 : Nat.Prime 34129332890315933 := by
  apply lucas_primality 34129332890315933 (2 : ZMod 34129332890315933)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (95868912613247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (95868912613247, 1)] : List FactorBlock).map factorBlockValue).prod) = 34129332890315933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_89
      · exact prime_decH_95868912613247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34129332890315933) ^ 17064666445157966 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34129332890315933) ^ 383475650452988 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34129332890315933) ^ 356 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_54314139857561237 : Nat.Prime 54314139857561237 := by
  apply lucas_primality 54314139857561237 (2 : ZMod 54314139857561237)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (47, 1), (800290856627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (47, 1), (800290856627, 1)] : List FactorBlock).map factorBlockValue).prod) = 54314139857561237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_19
      · exact prime_decH_47
      · exact prime_decH_800290856627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54314139857561237) ^ 27157069928780618 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54314139857561237) ^ 2858638939871644 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54314139857561237) ^ 1155619996969388 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54314139857561237) ^ 67868 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_83695859318210137 : Nat.Prime 83695859318210137 := by
  apply lucas_primality 83695859318210137 (15 : ZMod 83695859318210137)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1231, 1), (114013, 1), (24847363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1231, 1), (114013, 1), (24847363, 1)] : List FactorBlock).map factorBlockValue).prod) = 83695859318210137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_1231
      · exact prime_decH_114013
      · exact prime_decH_24847363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 83695859318210137) ^ 41847929659105068 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 83695859318210137) ^ 27898619772736712 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 83695859318210137) ^ 67990137545256 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 83695859318210137) ^ 734090492472 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (15 : ZMod 83695859318210137) ^ 3368400072 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_115731802574922943 : Nat.Prime 115731802574922943 := by
  apply lucas_primality 115731802574922943 (3 : ZMod 115731802574922943)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (378208505146807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (378208505146807, 1)] : List FactorBlock).map factorBlockValue).prod) = 115731802574922943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_378208505146807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115731802574922943) ^ 57865901287461471 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115731802574922943) ^ 38577267524974314 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115731802574922943) ^ 6807753092642526 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115731802574922943) ^ 306 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_13421
      · exact prime_decH_99611
      · exact prime_decH_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_5037757
      · exact prime_decH_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_29
      · exact prime_decH_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_518500159195792793 : Nat.Prime 518500159195792793 := by
  apply lucas_primality 518500159195792793 (3 : ZMod 518500159195792793)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod) = 518500159195792793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_131
      · exact prime_decH_5477
      · exact prime_decH_90332674877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518500159195792793) ^ 259250079597896396 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 3958016482410632 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 94668643271096 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 5739896 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_61717
      · exact prime_decH_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_17
      · exact prime_decH_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1249558476287426663 : Nat.Prime 1249558476287426663 := by
  apply lucas_primality 1249558476287426663 (5 : ZMod 1249558476287426663)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249558476287426663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_874459
      · exact prime_decH_102067880687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1249558476287426663) ^ 624779238143713331 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 178508353755346666 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 1428950329618 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 12242426 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1778110061930112629 : Nat.Prime 1778110061930112629 := by
  apply lucas_primality 1778110061930112629 (2 : ZMod 1778110061930112629)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (108923, 1), (1167211, 1), (3496469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (108923, 1), (1167211, 1), (3496469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1778110061930112629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_108923
      · exact prime_decH_1167211
      · exact prime_decH_3496469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1778110061930112629) ^ 889055030965056314 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 16324468311836 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 1523383571548 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 508544495012 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2499116952574853327 : Nat.Prime 2499116952574853327 := by
  apply lucas_primality 2499116952574853327 (5 : ZMod 2499116952574853327)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2499116952574853327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_1249558476287426663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2499116952574853327) ^ 1249558476287426663 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2499116952574853327) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2582665281154572547 : Nat.Prime 2582665281154572547 := by
  apply lucas_primality 2582665281154572547 (2 : ZMod 2582665281154572547)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (829, 1), (22575350790673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (829, 1), (22575350790673, 1)] : List FactorBlock).map factorBlockValue).prod) = 2582665281154572547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_23
      · exact prime_decH_829
      · exact prime_decH_22575350790673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2582665281154572547) ^ 1291332640577286273 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 860888427051524182 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 112289794832807502 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 3115398409112874 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 114402 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3775351412811012257 : Nat.Prime 3775351412811012257 := by
  apply lucas_primality 3775351412811012257 (3 : ZMod 3775351412811012257)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3775351412811012257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_52023863
      · exact prime_decH_2267800291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3775351412811012257) ^ 1887675706405506128 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 72569609312 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 1664763616 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_5875008263295773599 : Nat.Prime 5875008263295773599 := by
  apply lucas_primality 5875008263295773599 (3 : ZMod 5875008263295773599)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (223, 1), (1463629363053257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (223, 1), (1463629363053257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5875008263295773599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_223
      · exact prime_decH_1463629363053257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5875008263295773599) ^ 2937504131647886799 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 1958336087765257866 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 26345328534958626 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 4014 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_439
      · exact prime_decH_853
      · exact prime_decH_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_7
      · exact prime_decH_19
      · exact prime_decH_1823
      · exact prime_decH_3271
      · exact prime_decH_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_23
      · exact prime_decH_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_18752246585046131581 : Nat.Prime 18752246585046131581 := by
  apply lucas_primality 18752246585046131581 (2 : ZMod 18752246585046131581)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (77611, 1), (1342324511921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (77611, 1), (1342324511921, 1)] : List FactorBlock).map factorBlockValue).prod) = 18752246585046131581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_77611
      · exact prime_decH_1342324511921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18752246585046131581) ^ 9376123292523065790 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18752246585046131581) ^ 6250748861682043860 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18752246585046131581) ^ 3750449317009226316 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18752246585046131581) ^ 241618412145780 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18752246585046131581) ^ 13969980 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_45023731903529596433 : Nat.Prime 45023731903529596433 := by
  apply lucas_primality 45023731903529596433 (3 : ZMod 45023731903529596433)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) = 45023731903529596433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7411
      · exact prime_decH_93287
      · exact prime_decH_4070273261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45023731903529596433) ^ 22511865951764798216 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 6075257307182512 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 482636722196336 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 11061599312 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_58156383245098349833 : Nat.Prime 58156383245098349833 := by
  apply lucas_primality 58156383245098349833 (5 : ZMod 58156383245098349833)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (34129332890315933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (34129332890315933, 1)] : List FactorBlock).map factorBlockValue).prod) = 58156383245098349833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_71
      · exact prime_decH_34129332890315933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58156383245098349833) ^ 29078191622549174916 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 19385461081699449944 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 819103989367582392 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 1704 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_65689486876996052887 : Nat.Prime 65689486876996052887 := by
  apply lucas_primality 65689486876996052887 (3 : ZMod 65689486876996052887)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59659, 1), (2017843, 1), (10105057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59659, 1), (2017843, 1), (10105057, 1)] : List FactorBlock).map factorBlockValue).prod) = 65689486876996052887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_59659
      · exact prime_decH_2017843
      · exact prime_decH_10105057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65689486876996052887) ^ 32844743438498026443 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 21896495625665350962 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 1101082600730754 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 32554310160402 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 6500654758998 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_76768245926690061509 : Nat.Prime 76768245926690061509 := by
  apply lucas_primality 76768245926690061509 (2 : ZMod 76768245926690061509)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (311, 1), (977, 1), (19993, 1), (3159284287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (311, 1), (977, 1), (19993, 1), (3159284287, 1)] : List FactorBlock).map factorBlockValue).prod) = 76768245926690061509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_311
      · exact prime_decH_977
      · exact prime_decH_19993
      · exact prime_decH_3159284287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76768245926690061509) ^ 38384122963345030754 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 246843234490964828 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 78575482012988804 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 3839756211008356 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 24299252284 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_101627574192727747903 : Nat.Prime 101627574192727747903 := by
  apply lucas_primality 101627574192727747903 (3 : ZMod 101627574192727747903)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) = 101627574192727747903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_3833
      · exact prime_decH_1472991480313183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101627574192727747903) ^ 50813787096363873951 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 33875858064242582634 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 26513846645637294 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 68994 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_252913357496471033039 : Nat.Prime 252913357496471033039 := by
  apply lucas_primality 252913357496471033039 (13 : ZMod 252913357496471033039)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod) = 252913357496471033039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_337
      · exact prime_decH_601
      · exact prime_decH_40739
      · exact prime_decH_115901
      · exact prime_decH_132233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 252913357496471033039) ^ 126456678748235516519 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 750484740345611374 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 420820894336890238 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 6208138577198042 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 2182149916708838 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 1912634194917086 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_953929693745394630791 : Nat.Prime 953929693745394630791 := by
  apply lucas_primality 953929693745394630791 (7 : ZMod 953929693745394630791)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod) = 953929693745394630791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_19
      · exact prime_decH_73819
      · exact prime_decH_344873
      · exact prime_decH_197212943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 953929693745394630791) ^ 476964846872697315395 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 190785938749078926158 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 50206825986599717410 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 12922549665335410 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 2766031825470230 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 4837054197530 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_19
      · exact prime_decH_107
      · exact prime_decH_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_67
      · exact prime_decH_89
      · exact prime_decH_467
      · exact prime_decH_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_3881093604511367584661 : Nat.Prime 3881093604511367584661 := by
  apply lucas_primality 3881093604511367584661 (2 : ZMod 3881093604511367584661)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (373, 1), (7647103, 1), (68032800707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (373, 1), (7647103, 1), (68032800707, 1)] : List FactorBlock).map factorBlockValue).prod) = 3881093604511367584661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_373
      · exact prime_decH_7647103
      · exact prime_decH_68032800707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3881093604511367584661) ^ 1940546802255683792330 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881093604511367584661) ^ 776218720902273516932 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881093604511367584661) ^ 10405076687698036420 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881093604511367584661) ^ 507524693274220 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881093604511367584661) ^ 57047388380 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_6891984566505300835487 : Nat.Prime 6891984566505300835487 := by
  apply lucas_primality 6891984566505300835487 (5 : ZMod 6891984566505300835487)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6891984566505300835487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_11637001
      · exact prime_decH_296123742126743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6891984566505300835487) ^ 3445992283252650417743 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 592247484253486 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 23274002 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_29
      · exact prime_decH_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_12207876165556182456341 : Nat.Prime 12207876165556182456341 := by
  apply lucas_primality 12207876165556182456341 (2 : ZMod 12207876165556182456341)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (45119, 1), (13528531400913343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (45119, 1), (13528531400913343, 1)] : List FactorBlock).map factorBlockValue).prod) = 12207876165556182456341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_45119
      · exact prime_decH_13528531400913343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12207876165556182456341) ^ 6103938082778091228170 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 2441575233111236491268 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 270570628018266860 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 902380 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_12378824676074916524737 : Nat.Prime 12378824676074916524737 := by
  apply lucas_primality 12378824676074916524737 (5 : ZMod 12378824676074916524737)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (43517, 1), (493853323129583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (43517, 1), (493853323129583, 1)] : List FactorBlock).map factorBlockValue).prod) = 12378824676074916524737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_43517
      · exact prime_decH_493853323129583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12378824676074916524737) ^ 6189412338037458262368 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 4126274892024972174912 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 284459514122639808 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 25065792 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_113407983203946538337189 : Nat.Prime 113407983203946538337189 := by
  apply lucas_primality 113407983203946538337189 (2 : ZMod 113407983203946538337189)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1814357, 1), (2232352902117203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1814357, 1), (2232352902117203, 1)] : List FactorBlock).map factorBlockValue).prod) = 113407983203946538337189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_7
      · exact prime_decH_1814357
      · exact prime_decH_2232352902117203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113407983203946538337189) ^ 56703991601973269168594 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113407983203946538337189) ^ 16201140457706648333884 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113407983203946538337189) ^ 62505881259281684 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113407983203946538337189) ^ 50801996 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_301168454275224747175301 : Nat.Prime 301168454275224747175301 := by
  apply lucas_primality 301168454275224747175301 (3 : ZMod 301168454275224747175301)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod) = 301168454275224747175301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_241
      · exact prime_decH_266957
      · exact prime_decH_955333581581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 301168454275224747175301) ^ 150584227137612373587650 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 60233690855044949435060 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 43024064896460678167900 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1249661635996783183300 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1128153426489002900 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 315249521300 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1007384870571593615807227 : Nat.Prime 1007384870571593615807227 := by
  apply lucas_primality 1007384870571593615807227 (3 : ZMod 1007384870571593615807227)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2887, 1), (58156383245098349833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2887, 1), (58156383245098349833, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007384870571593615807227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_2887
      · exact prime_decH_58156383245098349833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1007384870571593615807227) ^ 503692435285796807903613 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 335794956857197871935742 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 348938299470590098998 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 17322 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1044313120839874805680913 : Nat.Prime 1044313120839874805680913 := by
  apply lucas_primality 1044313120839874805680913 (3 : ZMod 1044313120839874805680913)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (37, 1), (211, 1), (491, 1), (10499, 1), (129223, 1), (660547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (37, 1), (211, 1), (491, 1), (10499, 1), (129223, 1), (660547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1044313120839874805680913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_19
      · exact prime_decH_37
      · exact prime_decH_211
      · exact prime_decH_491
      · exact prime_decH_10499
      · exact prime_decH_129223
      · exact prime_decH_660547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1044313120839874805680913) ^ 522156560419937402840456 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 54963848465256568720048 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 28224678941618237991376 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 4949351283601302396592 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 2126910633075101437232 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 99467865590996743088 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 8081480238346693744 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044313120839874805680913) ^ 1580982308359397296 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_36489718645148835417017333 : Nat.Prime 36489718645148835417017333 := by
  apply lucas_primality 36489718645148835417017333 (2 : ZMod 36489718645148835417017333)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod) = 36489718645148835417017333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_73
      · exact prime_decH_131
      · exact prime_decH_953929693745394630791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36489718645148835417017333) ^ 18244859322574417708508666 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 499859159522586786534484 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 278547470573655232190972 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 38252 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_72979437290297670834034667 : Nat.Prime 72979437290297670834034667 := by
  apply lucas_primality 72979437290297670834034667 (2 : ZMod 72979437290297670834034667)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod) = 72979437290297670834034667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_36489718645148835417017333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72979437290297670834034667) ^ 36489718645148835417017333 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (2 : ZMod 72979437290297670834034667) ^ 2 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_131362987122535807501262401 : Nat.Prime 131362987122535807501262401 := by
  apply lucas_primality 131362987122535807501262401 (71 : ZMod 131362987122535807501262401)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 131362987122535807501262401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 131362987122535807501262401) ^ 65681493561267903750631200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 43787662374178602500420800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 26272597424507161500252480 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 18766141017505115357323200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 11942089738412346136478400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 10104845163271985192404800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 7727234536619753382427200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 6913841427501884605329600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 5711434222718948152228800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4529758176639165775905600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4237515713630187338750400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3550351003311778581115200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3203975295671605061006400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3054953188896181569796800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2794957172819910797899200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2478546926840298254740800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2226491307161623855953600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2153491592172718155758400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_159765795149030036150184001 : Nat.Prime 159765795149030036150184001 := by
  apply lucas_primality 159765795149030036150184001 (71 : ZMod 159765795149030036150184001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 159765795149030036150184001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 159765795149030036150184001) ^ 79882897574515018075092000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 53255265049676678716728000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 31953159029806007230036800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 22823685021290005164312000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 14524163195366366922744000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 12289676549925387396168000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 9397987949942943302952000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 8408726060475265060536000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 6946338919523045050008000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 5509165349966552970696000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 5153735327388065682264000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3896726710951952101224000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3715483608116977584888000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3399272237213405024472000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3014448965076038417928000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 2707894833034407392376000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 2619111395885738297544000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_214957615291422230456611201 : Nat.Prime 214957615291422230456611201 := by
  apply lucas_primality 214957615291422230456611201 (11 : ZMod 214957615291422230456611201)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 214957615291422230456611201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 214957615291422230456611201) ^ 107478807645711115228305600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 71652538430474076818870400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 42991523058284446091322240 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 30708230755917461493801600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 16535201176263248496662400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 12644565605377778262153600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 11313558699548538445084800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 9345983273540096976374400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 7412331561773180360572800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 6934116622303942917955200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5809665278146546769097600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5242868665644444645283200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4999014309102842568758400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4573566282796217669289600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4055804062102306235030400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3643349411719020855196800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3523895332646266073059200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_246305600854754639064867001 : Nat.Prime 246305600854754639064867001 := by
  apply lucas_primality 246305600854754639064867001 (103 : ZMod 246305600854754639064867001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 246305600854754639064867001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 246305600854754639064867001) ^ 123152800427377319532433500 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 82101866951584879688289000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 49261120170950927812973400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 35186514407822091294981000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 22391418259523149005897000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 18946584681134972235759000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 14488564756162037592051000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 12963452676566033634993000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 10708939167598027785429000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 8493296581198435829823000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 7945341963056601260157000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6656908131209584839591000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6007453679384259489387000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5728037229180340443369000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5240544699037332746061000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4647275487825559227639000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4174671200928044729913000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4037796735323846542047000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_288357776610444455490576001 : Nat.Prime 288357776610444455490576001 := by
  apply lucas_primality 288357776610444455490576001 (41 : ZMod 288357776610444455490576001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 288357776610444455490576001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 288357776610444455490576001) ^ 144178888305222227745288000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 96119258870148151830192000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 57671555322088891098115200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 41193968087206350784368000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 26214343328222223226416000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 22181367431572650422352000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 16962222153555556205328000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 15176725084760234499504000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 12537294635236715456112000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 9943371607256705361744000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 9301863761627240499696000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 7793453421903904202448000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 6705994804894057104432000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 6135271842775413946608000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 5440712766234801046992000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 4887419942549906025264000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 4727176665744991073616000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_407678235897524919831504001 : Nat.Prime 407678235897524919831504001 := by
  apply lucas_primality 407678235897524919831504001 (67 : ZMod 407678235897524919831504001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 407678235897524919831504001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 407678235897524919831504001) ^ 203839117948762459915752000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 135892745299174973277168000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 81535647179504983966300800 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 58239747985360702833072000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 37061657808865901802864000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 31359864299809609217808000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 23981072699854407048912000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 21456749257764469464816000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 17725140691196735644848000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 13150910835404029671984000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 11018330699933105941392000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9943371607256705361744000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9480889206919184182128000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 8674005019096274890032000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 7692042186745753204368000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6909800608432625759856000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6683249768811883931664000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_437876623741786025004208001 : Nat.Prime 437876623741786025004208001 := by
  apply lucas_primality 437876623741786025004208001 (12 : ZMod 437876623741786025004208001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 437876623741786025004208001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 437876623741786025004208001) ^ 218938311870893012502104000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 87575324748357205000841600 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 62553803391683717857744000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 39806965794707820454928000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 33682817210906617308016000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 25757448455399177941424000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 23046138091672948684432000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 19038114075729827174096000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 15099193922130552586352000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 14125052378767291129168000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 11834503344372595270384000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10679917652238683536688000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10183177296320605232656000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 9316523909399702659664000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 8261823089467660849136000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7421637690538746186512000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7178305307242393852528000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_909436064694478667316432001 : Nat.Prime 909436064694478667316432001 := by
  apply lucas_primality 909436064694478667316432001 (26 : ZMod 909436064694478667316432001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478667316432001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 909436064694478667316432001) ^ 454718032347239333658216000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 303145354898159555772144000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 181887212938895733463286400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 129919437813496952473776000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 82676005881316242483312000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 53496239099675215724496000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 47865056036551508806128000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 39540698464977333361584000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 31359864299809609217808000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 29336647248208989268272000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 24579353099850774792336000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 22181367431572650422352000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 21149675923127410867824000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 19349703504137843985456000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 17159171031971295609744000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 15414170588042011310448000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 14908787945811125693712000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1074788076457111152283056001 : Nat.Prime 1074788076457111152283056001 := by
  apply lucas_primality 1074788076457111152283056001 (67 : ZMod 1074788076457111152283056001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074788076457111152283056001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1074788076457111152283056001) ^ 537394038228555576141528000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 358262692152370384094352000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 214957615291422230456611200 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 153541153779587307469008000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 82676005881316242483312000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 63222828026888891310768000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 56567793497742692225424000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 46729916367700484881872000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 37061657808865901802864000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 34670583111519714589776000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 29048326390732733845488000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 26214343328222223226416000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 24995071545514212843792000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 22867831413981088346448000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 20279020310511531175152000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 18216747058595104275984000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 17619476663231330365296000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem prime_decH_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← decHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_decH_2
      · exact prime_decH_3
      · exact prime_decH_5
      · exact prime_decH_7
      · exact prime_decH_11
      · exact prime_decH_13
      · exact prime_decH_17
      · exact prime_decH_19
      · exact prime_decH_23
      · exact prime_decH_29
      · exact prime_decH_31
      · exact prime_decH_37
      · exact prime_decH_41
      · exact prime_decH_43
      · exact prime_decH_47
      · exact prime_decH_53
      · exact prime_decH_59
      · exact prime_decH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← decHFastPow_eq_pow]
      decide

private theorem phi_decH_11822668841028222675113616000 : Nat.totient 11822668841028222675113616000 = 1555713684593606393856000000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_5, prime_decH_7, prime_decH_11, prime_decH_13, prime_decH_17, prime_decH_19, prime_decH_23, prime_decH_29, prime_decH_31, prime_decH_37, prime_decH_41, prime_decH_43, prime_decH_47, prime_decH_53, prime_decH_59, prime_decH_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616001 : Nat.totient 11822668841028222675113616001 = 11802992225090850041226588048 := by
  rw [← show ((([(859, 1), (1997, 1), (6891984566505300835487, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_859, prime_decH_1997, prime_decH_6891984566505300835487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616002 : Nat.totient 11822668841028222675113616002 = 5911293274574380552724110512 := by
  rw [← show ((([(2, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_143669, prime_decH_13852339783, prime_decH_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616003 : Nat.totient 11822668841028222675113616003 = 7881757901737286031539712000 := by
  rw [← show ((([(3, 1), (374681, 1), (27212041, 1), (386519565736481, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_374681, prime_decH_27212041, prime_decH_386519565736481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616004 : Nat.totient 11822668841028222675113616004 = 5883617151582452919630148608 := by
  rw [← show ((([(2, 2), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_223, prime_decH_5113, prime_decH_101287, prime_decH_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616005 : Nat.totient 11822668841028222675113616005 = 9458090075438874484030430208 := by
  rw [← show ((([(5, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_210193, prime_decH_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616006 : Nat.totient 11822668841028222675113616006 = 3886904484868391081403667200 := by
  rw [← show ((([(2, 1), (3, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_73, prime_decH_13737811, prime_decH_68784581, prime_decH_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616007 : Nat.totient 11822668841028222675113616007 = 10118658610368043988843969280 := by
  rw [← show ((([(7, 1), (673, 1), (889647091, 1), (2820880298726107, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_7, prime_decH_673, prime_decH_889647091, prime_decH_2820880298726107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616008 : Nat.totient 11822668841028222675113616008 = 5911334420514111337556808000 := by
  rw [← show ((([(2, 3), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616009 : Nat.totient 11822668841028222675113616009 = 7881779227319008179733605912 := by
  rw [← show ((([(3, 2), (237841108607, 1), (5523140549247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_237841108607, prime_decH_5523140549247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616010 : Nat.totient 11822668841028222675113616010 = 4682219311413182558003904768 := by
  rw [← show ((([(2, 1), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_103, prime_decH_5009, prime_decH_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616011 : Nat.totient 11822668841028222675113616011 = 10747880764571111522830560000 := by
  rw [← show ((([(11, 1), (1074788076457111152283056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_11, prime_decH_1074788076457111152283056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616012 : Nat.totient 11822668841028222675113616012 = 3920512107669351327533481984 := by
  rw [← show ((([(2, 2), (3, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_283, prime_decH_613, prime_decH_85303, prime_decH_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616013 : Nat.totient 11822668841028222675113616013 = 10913232776333744007797184000 := by
  rw [← show ((([(13, 1), (909436064694478667316432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_13, prime_decH_909436064694478667316432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616014 : Nat.totient 11822668841028222675113616014 = 5021926290412878865174732800 := by
  rw [← show ((([(2, 1), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_7, prime_decH_113, prime_decH_54421, prime_decH_97654321, prime_decH_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616015 : Nat.totient 11822668841028222675113616015 = 6286198917043595648577024000 := by
  rw [← show ((([(3, 1), (5, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_5, prime_decH_421, prime_decH_1483, prime_decH_2072201, prime_decH_2567179, prime_decH_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616016 : Nat.totient 11822668841028222675113616016 = 5840109395431937154145971200 := by
  rw [← show ((([(2, 4), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_83, prime_decH_1433741, prime_decH_106163831, prime_decH_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616017 : Nat.totient 11822668841028222675113616017 = 11127217732275111403740537600 := by
  rw [← show ((([(17, 1), (24330664621, 1), (28583317353999781, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_17, prime_decH_24330664621, prime_decH_28583317353999781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616018 : Nat.totient 11822668841028222675113616018 = 3933854863788684518599788288 := by
  rw [← show ((([(2, 1), (3, 2), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_569, prime_decH_37039, prime_decH_1544987, prime_decH_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616019 : Nat.totient 11822668841028222675113616019 = 11200418434272921159565566720 := by
  rw [← show ((([(19, 1), (2428859, 1), (167470561, 1), (1529752406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_19, prime_decH_2428859, prime_decH_167470561, prime_decH_1529752406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616020 : Nat.totient 11822668841028222675113616020 = 4729067532543297963057648800 := by
  rw [← show ((([(2, 2), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_1222615931, prime_decH_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616021 : Nat.totient 11822668841028222675113616021 = 6755810736312438095034832944 := by
  rw [← show ((([(3, 1), (7, 1), (225273263, 1), (2499116952574853327, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_7, prime_decH_225273263, prime_decH_2499116952574853327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616022 : Nat.totient 11822668841028222675113616022 = 5298251080928055058366958400 := by
  rw [← show ((([(2, 1), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_11, prime_decH_71, prime_decH_26687336297, prime_decH_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616023 : Nat.totient 11822668841028222675113616023 = 11294998259025162011501587680 := by
  rw [← show ((([(23, 1), (829, 1), (56624411, 1), (10950386820164879, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_23, prime_decH_829, prime_decH_56624411, prime_decH_10950386820164879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616024 : Nat.totient 11822668841028222675113616024 = 3904729534419347717874537984 := by
  rw [← show ((([(2, 3), (3, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_109, prime_decH_762563, prime_decH_500452427, prime_decH_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616025 : Nat.totient 11822668841028222675113616025 = 9416376836876748091987690560 := by
  rw [← show ((([(5, 2), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_239, prime_decH_4327, prime_decH_1214459, prime_decH_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616026 : Nat.totient 11822668841028222675113616026 = 5444337797574560906077056000 := by
  rw [← show ((([(2, 1), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_13, prime_decH_599, prime_decH_1811, prime_decH_33809, prime_decH_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616027 : Nat.totient 11822668841028222675113616027 = 7881779227352148450075744000 := by
  rw [← show ((([(3, 3), (437876623741786025004208001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_437876623741786025004208001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616028 : Nat.totient 11822668841028222675113616028 = 5066858071694637935320021248 := by
  rw [← show ((([(2, 2), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_7, prime_decH_1671268889, prime_decH_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616029 : Nat.totient 11822668841028222675113616029 = 11414990605130697755282112000 := by
  rw [← show ((([(29, 1), (407678235897524919831504001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_29, prime_decH_407678235897524919831504001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616030 : Nat.totient 11822668841028222675113616030 = 3152711690940859380030297600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_5, prime_decH_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616031 : Nat.totient 11822668841028222675113616031 = 11378061674065835775260208000 := by
  rw [← show ((([(31, 1), (181, 1), (609781, 1), (21346979, 1), (161869470179, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_31, prime_decH_181, prime_decH_609781, prime_decH_21346979, prime_decH_161869470179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616032 : Nat.totient 11822668841028222675113616032 = 5911334406862518913240200192 := by
  rw [← show ((([(2, 5), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_433014277, prime_decH_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616033 : Nat.totient 11822668841028222675113616033 = 7149905854645094396537980800 := by
  rw [← show ((([(3, 1), (11, 1), (467, 1), (1479571, 1), (518500159195792793, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_11, prime_decH_467, prime_decH_1479571, prime_decH_518500159195792793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616034 : Nat.totient 11822668841028222675113616034 = 5563607240325035351648872512 := by
  rw [← show ((([(2, 1), (17, 1), (3421567, 1), (101627574192727747903, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_17, prime_decH_3421567, prime_decH_101627574192727747903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616035 : Nat.totient 11822668841028222675113616035 = 8106889790731887118593367008 := by
  rw [← show ((([(5, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_7, prime_decH_97523, prime_decH_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616036 : Nat.totient 11822668841028222675113616036 = 3940889073391291382595185664 := by
  rw [← show ((([(2, 2), (3, 2), (7294097, 1), (45023731903529596433, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_7294097, prime_decH_45023731903529596433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616037 : Nat.totient 11822668841028222675113616037 = 11503137250727935004418631632 := by
  rw [← show ((([(37, 1), (5686502827427, 1), (56191230356363, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_37, prime_decH_5686502827427, prime_decH_56191230356363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616038 : Nat.totient 11822668841028222675113616038 = 5600211555672956774409463296 := by
  rw [← show ((([(2, 1), (19, 1), (9278485297, 1), (33531643827487633, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_19, prime_decH_9278485297, prime_decH_33531643827487633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616039 : Nat.totient 11822668841028222675113616039 = 7237488988703119677715630080 := by
  rw [← show ((([(3, 1), (13, 1), (193, 1), (23911, 1), (65689486876996052887, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_13, prime_decH_193, prime_decH_23911, prime_decH_65689486876996052887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616040 : Nat.totient 11822668841028222675113616040 = 4729067310472396597300764672 := by
  rw [← show ((([(2, 3), (5, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_20930737, prime_decH_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616041 : Nat.totient 11822668841028222675113616041 = 11534311064417778219623040000 := by
  rw [← show ((([(41, 1), (288357776610444455490576001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_41, prime_decH_288357776610444455490576001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616042 : Nat.totient 11822668841028222675113616042 = 3313933950734047119790080000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (97, 1), (139, 1), (659, 1), (55001, 1), (576001613200633, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_7, prime_decH_97, prime_decH_139, prime_decH_659, prime_decH_55001, prime_decH_576001613200633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616043 : Nat.totient 11822668841028222675113616043 = 11546985670968966383020746240 := by
  rw [← show ((([(43, 1), (15661, 1), (417616597, 1), (42038753447953, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_43, prime_decH_15661, prime_decH_417616597, prime_decH_42038753447953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616044 : Nat.totient 11822668841028222675113616044 = 5370176130405898412111884800 := by
  rw [← show ((([(2, 2), (11, 1), (1471, 1), (48383, 1), (3775351412811012257, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_11, prime_decH_1471, prime_decH_48383, prime_decH_3775351412811012257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616045 : Nat.totient 11822668841028222675113616045 = 6192819318588176905531084800 := by
  rw [← show ((([(3, 2), (5, 1), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_5, prime_decH_67, prime_decH_491, prime_decH_1061, prime_decH_9492089, prime_decH_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616046 : Nat.totient 11822668841028222675113616046 = 5654319691825232192232981216 := by
  rw [← show ((([(2, 1), (23, 1), (56297287, 1), (64144099, 1), (71172712477, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_23, prime_decH_56297287, prime_decH_64144099, prime_decH_71172712477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616047 : Nat.totient 11822668841028222675113616047 = 11571122695470066236741125792 := by
  rw [← show ((([(47, 1), (2729747741957, 1), (92149960118093, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_47, prime_decH_2729747741957, prime_decH_92149960118093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616048 : Nat.totient 11822668841028222675113616048 = 3940889613676074225037872000 := by
  rw [← show ((([(2, 4), (3, 1), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_246305600854754639064867001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616049 : Nat.totient 11822668841028222675113616049 = 10082792952677180259896692320 := by
  rw [← show ((([(7, 2), (199, 1), (236131189291, 1), (5134675637989, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_7, prime_decH_199, prime_decH_236131189291, prime_decH_5134675637989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616050 : Nat.totient 11822668841028222675113616050 = 4729067528857841659119593040 := by
  rw [← show ((([(2, 1), (5, 2), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_626080687, prime_decH_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616051 : Nat.totient 11822668841028222675113616051 = 7405476120006957282903072768 := by
  rw [← show ((([(3, 1), (17, 1), (719, 1), (5923, 1), (6733, 1), (7482733, 1), (1080452957, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_17, prime_decH_719, prime_decH_5923, prime_decH_6733, prime_decH_7482733, prime_decH_1080452957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616052 : Nat.totient 11822668841028222675113616052 = 5456616387944359692662572128 := by
  rw [← show ((([(2, 2), (13, 1), (24522826583, 1), (9271321778674247, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_13, prime_decH_24522826583, prime_decH_9271321778674247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616053 : Nat.totient 11822668841028222675113616053 = 11534796610423092818020450176 := by
  rw [← show ((([(53, 1), (179, 1), (14889587, 1), (83695859318210137, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_53, prime_decH_179, prime_decH_14889587, prime_decH_83695859318210137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616054 : Nat.totient 11822668841028222675113616054 = 3940889613676074225037871964 := by
  rw [← show ((([(2, 1), (3, 4), (72979437290297670834034667, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_72979437290297670834034667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616055 : Nat.totient 11822668841028222675113616055 = 8598304611656889218264448000 := by
  rw [← show ((([(5, 1), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_11, prime_decH_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616056 : Nat.totient 11822668841028222675113616056 = 5059630031823775752545040000 := by
  rw [← show ((([(2, 3), (7, 1), (701, 1), (301168454275224747175301, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_7, prime_decH_701, prime_decH_301168454275224747175301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616057 : Nat.totient 11822668841028222675113616057 = 7466948066621158311697041600 := by
  rw [← show ((([(3, 1), (19, 1), (11060821, 1), (18752246585046131581, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_19, prime_decH_11060821, prime_decH_18752246585046131581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616058 : Nat.totient 11822668841028222675113616058 = 5642483946057389443548856320 := by
  rw [← show ((([(2, 1), (29, 1), (89, 1), (6397, 1), (894938237, 1), (400062744481, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_29, prime_decH_89, prime_decH_6397, prime_decH_894938237, prime_decH_400062744481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616059 : Nat.totient 11822668841028222675113616059 = 11620214883237783019375360000 := by
  rw [← show ((([(59, 1), (5801, 1), (179351, 1), (8001839, 1), (24069498209, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_59, prime_decH_5801, prime_decH_179351, prime_decH_8001839, prime_decH_24069498209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616060 : Nat.totient 11822668841028222675113616060 = 3144933657121987422886215168 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_5, prime_decH_409, prime_decH_45127, prime_decH_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616061 : Nat.totient 11822668841028222675113616061 = 11622050118740441248795026240 := by
  rw [← show ((([(61, 1), (1709, 1), (113407983203946538337189, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_61, prime_decH_1709, prime_decH_113407983203946538337189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616062 : Nat.totient 11822668841028222675113616062 = 5720533497321772806330600960 := by
  rw [← show ((([(2, 1), (31, 1), (50753, 1), (9003352679, 1), (417309099223, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_31, prime_decH_50753, prime_decH_9003352679, prime_decH_417309099223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616063 : Nat.totient 11822668841028222675113616063 = 6695279712052422871307203584 := by
  rw [← show ((([(3, 2), (7, 1), (137, 1), (617, 1), (19183, 1), (115731802574922943, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_7, prime_decH_137, prime_decH_617, prime_decH_19183, prime_decH_115731802574922943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616064 : Nat.totient 11822668841028222675113616064 = 5910938298124476940227538944 := by
  rw [← show ((([(2, 6), (14923, 1), (12378824676074916524737, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_14923, prime_decH_12378824676074916524737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616065 : Nat.totient 11822668841028222675113616065 = 8730586221064974309841219776 := by
  rw [← show ((([(5, 1), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_13, prime_decH_4887540332063, prime_decH_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616066 : Nat.totient 11822668841028222675113616066 = 3549131971912506178150378560 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (107, 1), (284957, 1), (5875008263295773599, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_11, prime_decH_107, prime_decH_284957, prime_decH_5875008263295773599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616067 : Nat.totient 11822668841028222675113616067 = 11813511010435462116743412000 := by
  rw [← show ((([(1291, 1), (168607301, 1), (54314139857561237, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_1291, prime_decH_168607301, prime_decH_54314139857561237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616068 : Nat.totient 11822668841028222675113616068 = 5468982694728765971981414400 := by
  rw [← show ((([(2, 2), (17, 1), (79, 1), (227, 1), (3222797, 1), (3008297016953401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_17, prime_decH_79, prime_decH_227, prime_decH_3222797, prime_decH_3008297016953401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616069 : Nat.totient 11822668841028222675113616069 = 7538246723935614281314008960 := by
  rw [← show ((([(3, 1), (23, 1), (8969, 1), (1282511, 1), (14895713529653239, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_23, prime_decH_8969, prime_decH_1282511, prime_decH_14895713529653239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616070 : Nat.totient 11822668841028222675113616070 = 4044693647204004540427678080 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_7, prime_decH_461, prime_decH_13492702567, prime_decH_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616071 : Nat.totient 11822668841028222675113616071 = 11822668704789502244516314560 := by
  rw [← show ((([(88478713, 1), (5564150981, 1), (24014736307, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_88478713, prime_decH_5564150981, prime_decH_24014736307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616072 : Nat.totient 11822668841028222675113616072 = 3916712376782355978258494688 := by
  rw [← show ((([(2, 3), (3, 2), (163, 1), (1007384870571593615807227, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_163, prime_decH_1007384870571593615807227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616073 : Nat.totient 11822668841028222675113616073 = 11821624527907382800307923840 := by
  rw [← show ((([(11321, 1), (1044313120839874805680913, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_11321, prime_decH_1044313120839874805680913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616074 : Nat.totient 11822668841028222675113616074 = 5751568625365081301406624000 := by
  rw [← show ((([(2, 1), (37, 1), (159765795149030036150184001, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_37, prime_decH_159765795149030036150184001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616075 : Nat.totient 11822668841028222675113616075 = 6305413265347418901194342560 := by
  rw [← show ((([(3, 1), (5, 2), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_5, prime_decH_623279, prime_decH_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616076 : Nat.totient 11822668841028222675113616076 = 5566627975887932832394217856 := by
  rw [← show ((([(2, 2), (19, 2), (167, 1), (115319, 1), (5026759, 1), (84575179597, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_19, prime_decH_167, prime_decH_115319, prime_decH_5026759, prime_decH_84575179597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616077 : Nat.totient 11822668841028222675113616077 = 9212463636788419152745723200 := by
  rw [← show ((([(7, 1), (11, 1), (1997173, 1), (9427111, 1), (8155122571867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_7, prime_decH_11, prime_decH_1997173, prime_decH_9427111, prime_decH_8155122571867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616078 : Nat.totient 11822668841028222675113616078 = 3637744258430281606526426208 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (10464329423, 1), (14484700483141487, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_13, prime_decH_10464329423, prime_decH_14484700483141487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616079 : Nat.totient 11822668841028222675113616079 = 11644419822840962684981701632 := by
  rw [← show ((([(73, 1), (1297, 1), (1663, 1), (39119, 1), (1919431841927447, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_73, prime_decH_1297, prime_decH_1663, prime_decH_39119, prime_decH_1919431841927447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616080 : Nat.totient 11822668841028222675113616080 = 4704308003834607887353205760 := by
  rw [← show ((([(2, 4), (5, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_5, prime_decH_191, prime_decH_282045737, prime_decH_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616081 : Nat.totient 11822668841028222675113616081 = 7833226746359711241589616640 := by
  rw [← show ((([(3, 3), (257, 1), (439, 1), (3881093604511367584661, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_257, prime_decH_439, prime_decH_3881093604511367584661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616082 : Nat.totient 11822668841028222675113616082 = 5767155461084486629363596160 := by
  rw [← show ((([(2, 1), (41, 1), (81085469, 1), (1778110061930112629, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_41, prime_decH_81085469, prime_decH_1778110061930112629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616083 : Nat.totient 11822668841028222675113616083 = 11773612123838735731843173120 := by
  rw [← show ((([(241, 1), (1853410441097, 1), (26468350503979, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_241, prime_decH_1853410441097, prime_decH_26468350503979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616084 : Nat.totient 11822668841028222675113616084 = 3377903540713018523712698496 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1833389, 1), (76768245926690061509, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_7, prime_decH_1833389, prime_decH_76768245926690061509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616085 : Nat.totient 11822668841028222675113616085 = 8854602014048170665217720320 := by
  rw [← show ((([(5, 1), (17, 1), (229, 1), (1669, 1), (2963, 1), (108608761, 1), (1130858507, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_17, prime_decH_229, prime_decH_1669, prime_decH_2963, prime_decH_108608761, prime_decH_1130858507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616086 : Nat.totient 11822668841028222675113616086 = 5773348796214829807252312800 := by
  rw [← show ((([(2, 1), (43, 1), (11261, 1), (12207876165556182456341, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_43, prime_decH_11261, prime_decH_12207876165556182456341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616087 : Nat.totient 11822668841028222675113616087 = 7609631639364461507200942080 := by
  rw [← show ((([(3, 1), (29, 1), (21121, 1), (4244609, 1), (1515807687150209, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_29, prime_decH_21121, prime_decH_4244609, prime_decH_1515807687150209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616088 : Nat.totient 11822668841028222675113616088 = 5373898863986747668736733120 := by
  rw [← show ((([(2, 3), (11, 2), (129439, 1), (7795619827, 1), (12103873247, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_11, prime_decH_129439, prime_decH_7795619827, prime_decH_12103873247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616089 : Nat.totient 11822668841028222675113616089 = 11822666461365197668306001536 := by
  rw [← show ((([(5265209, 1), (88077317, 1), (25493873893613, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5265209, prime_decH_88077317, prime_decH_25493873893613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616090 : Nat.totient 11822668841028222675113616090 = 3152711690940859380030297600 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_5, prime_decH_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616091 : Nat.totient 11822668841028222675113616091 = 9353394478134939404832251904 := by
  rw [← show ((([(7, 1), (13, 2), (13669, 1), (77489, 1), (9435262352856497, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_7, prime_decH_13, prime_decH_13669, prime_decH_77489, prime_decH_9435262352856497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616092 : Nat.totient 11822668841028222675113616092 = 5610450220484849057071353600 := by
  rw [← show ((([(2, 2), (23, 1), (131, 1), (8221, 1), (230189, 1), (518378746886659, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_23, prime_decH_131, prime_decH_8221, prime_decH_230189, prime_decH_518378746886659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616093 : Nat.totient 11822668841028222675113616093 = 7495602867084100330315353600 := by
  rw [← show ((([(3, 1), (31, 1), (71, 1), (307, 1), (1015645049, 1), (5742406021717, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_3, prime_decH_31, prime_decH_71, prime_decH_307, prime_decH_1015645049, prime_decH_5742406021717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616094 : Nat.totient 11822668841028222675113616094 = 5750533669087696697303531520 := by
  rw [← show ((([(2, 1), (47, 1), (337, 1), (449, 1), (1163, 1), (90191, 1), (7924438741469, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_47, prime_decH_337, prime_decH_449, prime_decH_1163, prime_decH_90191, prime_decH_7924438741469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616095 : Nat.totient 11822668841028222675113616095 = 8862881651545779157856256000 := by
  rw [← show ((([(5, 1), (19, 1), (149, 1), (349, 1), (1213, 1), (2897, 1), (6151, 1), (110719776691, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_5, prime_decH_19, prime_decH_149, prime_decH_349, prime_decH_1213, prime_decH_2897, prime_decH_6151, prime_decH_110719776691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616096 : Nat.totient 11822668841028222675113616096 = 3940889531030785226565650304 := by
  rw [← show ((([(2, 5), (3, 1), (47684383, 1), (2582665281154572547, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_3, prime_decH_47684383, prime_decH_2582665281154572547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616097 : Nat.totient 11822668841028222675113616097 = 11801669410417134290999430528 := by
  rw [← show ((([(563, 1), (627237883, 1), (33479182882496993, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_563, prime_decH_627237883, prime_decH_33479182882496993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_decH_11822668841028222675113616098 : Nat.totient 11822668841028222675113616098 = 5066813447778688107235788096 := by
  rw [← show ((([(2, 1), (7, 2), (118687, 1), (2617129, 1), (388383853927687, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028222675113616098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_decH_2, prime_decH_7, prime_decH_118687, prime_decH_2617129, prime_decH_388383853927687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64DecH : certifiedKill 1 11822668841028222675113615999 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_decH_11822668841028222675113616000, phi_decH_11822668841028222675113616001, phi_decH_11822668841028222675113616002,
    phi_decH_11822668841028222675113616003, phi_decH_11822668841028222675113616004, phi_decH_11822668841028222675113616005,
    phi_decH_11822668841028222675113616006, phi_decH_11822668841028222675113616007, phi_decH_11822668841028222675113616008,
    phi_decH_11822668841028222675113616009, phi_decH_11822668841028222675113616010, phi_decH_11822668841028222675113616011,
    phi_decH_11822668841028222675113616012, phi_decH_11822668841028222675113616013, phi_decH_11822668841028222675113616014,
    phi_decH_11822668841028222675113616015, phi_decH_11822668841028222675113616016, phi_decH_11822668841028222675113616017,
    phi_decH_11822668841028222675113616018, phi_decH_11822668841028222675113616019, phi_decH_11822668841028222675113616020,
    phi_decH_11822668841028222675113616021, phi_decH_11822668841028222675113616022, phi_decH_11822668841028222675113616023,
    phi_decH_11822668841028222675113616024, phi_decH_11822668841028222675113616025, phi_decH_11822668841028222675113616026,
    phi_decH_11822668841028222675113616027, phi_decH_11822668841028222675113616028, phi_decH_11822668841028222675113616029,
    phi_decH_11822668841028222675113616030, phi_decH_11822668841028222675113616031, phi_decH_11822668841028222675113616032,
    phi_decH_11822668841028222675113616033, phi_decH_11822668841028222675113616034, phi_decH_11822668841028222675113616035,
    phi_decH_11822668841028222675113616036, phi_decH_11822668841028222675113616037, phi_decH_11822668841028222675113616038,
    phi_decH_11822668841028222675113616039, phi_decH_11822668841028222675113616040, phi_decH_11822668841028222675113616041,
    phi_decH_11822668841028222675113616042, phi_decH_11822668841028222675113616043, phi_decH_11822668841028222675113616044,
    phi_decH_11822668841028222675113616045, phi_decH_11822668841028222675113616046, phi_decH_11822668841028222675113616047,
    phi_decH_11822668841028222675113616048, phi_decH_11822668841028222675113616049, phi_decH_11822668841028222675113616050,
    phi_decH_11822668841028222675113616051, phi_decH_11822668841028222675113616052, phi_decH_11822668841028222675113616053,
    phi_decH_11822668841028222675113616054, phi_decH_11822668841028222675113616055, phi_decH_11822668841028222675113616056,
    phi_decH_11822668841028222675113616057, phi_decH_11822668841028222675113616058, phi_decH_11822668841028222675113616059,
    phi_decH_11822668841028222675113616060, phi_decH_11822668841028222675113616061, phi_decH_11822668841028222675113616062,
    phi_decH_11822668841028222675113616063, phi_decH_11822668841028222675113616064, phi_decH_11822668841028222675113616065,
    phi_decH_11822668841028222675113616066, phi_decH_11822668841028222675113616067, phi_decH_11822668841028222675113616068,
    phi_decH_11822668841028222675113616069, phi_decH_11822668841028222675113616070, phi_decH_11822668841028222675113616071,
    phi_decH_11822668841028222675113616072, phi_decH_11822668841028222675113616073, phi_decH_11822668841028222675113616074,
    phi_decH_11822668841028222675113616075, phi_decH_11822668841028222675113616076, phi_decH_11822668841028222675113616077,
    phi_decH_11822668841028222675113616078, phi_decH_11822668841028222675113616079, phi_decH_11822668841028222675113616080,
    phi_decH_11822668841028222675113616081, phi_decH_11822668841028222675113616082, phi_decH_11822668841028222675113616083,
    phi_decH_11822668841028222675113616084, phi_decH_11822668841028222675113616085, phi_decH_11822668841028222675113616086,
    phi_decH_11822668841028222675113616087, phi_decH_11822668841028222675113616088, phi_decH_11822668841028222675113616089,
    phi_decH_11822668841028222675113616090, phi_decH_11822668841028222675113616091, phi_decH_11822668841028222675113616092,
    phi_decH_11822668841028222675113616093, phi_decH_11822668841028222675113616094, phi_decH_11822668841028222675113616095,
    phi_decH_11822668841028222675113616096, phi_decH_11822668841028222675113616097, phi_decH_11822668841028222675113616098]

end TotientTailPeriodKiller
end Erdos249257
