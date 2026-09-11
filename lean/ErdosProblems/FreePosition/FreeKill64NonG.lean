import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def nonGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem nonGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    nonGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [nonGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [nonGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then nonGFastPow a n * nonGFastPow a n * a
        else nonGFastPow a n * nonGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_nonG_2 : Nat.Prime 2 := by norm_num
private theorem prime_nonG_3 : Nat.Prime 3 := by norm_num
private theorem prime_nonG_5 : Nat.Prime 5 := by norm_num
private theorem prime_nonG_7 : Nat.Prime 7 := by norm_num
private theorem prime_nonG_11 : Nat.Prime 11 := by norm_num
private theorem prime_nonG_13 : Nat.Prime 13 := by norm_num
private theorem prime_nonG_17 : Nat.Prime 17 := by norm_num
private theorem prime_nonG_19 : Nat.Prime 19 := by norm_num
private theorem prime_nonG_23 : Nat.Prime 23 := by norm_num
private theorem prime_nonG_29 : Nat.Prime 29 := by norm_num
private theorem prime_nonG_31 : Nat.Prime 31 := by norm_num
private theorem prime_nonG_37 : Nat.Prime 37 := by norm_num
private theorem prime_nonG_41 : Nat.Prime 41 := by norm_num
private theorem prime_nonG_43 : Nat.Prime 43 := by norm_num
private theorem prime_nonG_47 : Nat.Prime 47 := by norm_num
private theorem prime_nonG_53 : Nat.Prime 53 := by norm_num
private theorem prime_nonG_59 : Nat.Prime 59 := by norm_num
private theorem prime_nonG_61 : Nat.Prime 61 := by norm_num
private theorem prime_nonG_67 : Nat.Prime 67 := by norm_num
private theorem prime_nonG_71 : Nat.Prime 71 := by norm_num
private theorem prime_nonG_73 : Nat.Prime 73 := by norm_num
private theorem prime_nonG_79 : Nat.Prime 79 := by norm_num
private theorem prime_nonG_83 : Nat.Prime 83 := by norm_num
private theorem prime_nonG_89 : Nat.Prime 89 := by norm_num
private theorem prime_nonG_97 : Nat.Prime 97 := by norm_num
private theorem prime_nonG_101 : Nat.Prime 101 := by norm_num
private theorem prime_nonG_103 : Nat.Prime 103 := by norm_num
private theorem prime_nonG_107 : Nat.Prime 107 := by norm_num
private theorem prime_nonG_109 : Nat.Prime 109 := by norm_num
private theorem prime_nonG_113 : Nat.Prime 113 := by norm_num
private theorem prime_nonG_127 : Nat.Prime 127 := by norm_num
private theorem prime_nonG_131 : Nat.Prime 131 := by norm_num
private theorem prime_nonG_137 : Nat.Prime 137 := by norm_num
private theorem prime_nonG_139 : Nat.Prime 139 := by norm_num
private theorem prime_nonG_149 : Nat.Prime 149 := by norm_num
private theorem prime_nonG_151 : Nat.Prime 151 := by norm_num
private theorem prime_nonG_157 : Nat.Prime 157 := by norm_num
private theorem prime_nonG_163 : Nat.Prime 163 := by norm_num
private theorem prime_nonG_167 : Nat.Prime 167 := by norm_num
private theorem prime_nonG_173 : Nat.Prime 173 := by norm_num
private theorem prime_nonG_179 : Nat.Prime 179 := by norm_num
private theorem prime_nonG_181 : Nat.Prime 181 := by norm_num
private theorem prime_nonG_191 : Nat.Prime 191 := by norm_num
private theorem prime_nonG_193 : Nat.Prime 193 := by norm_num
private theorem prime_nonG_197 : Nat.Prime 197 := by norm_num
private theorem prime_nonG_199 : Nat.Prime 199 := by norm_num
private theorem prime_nonG_211 : Nat.Prime 211 := by norm_num
private theorem prime_nonG_223 : Nat.Prime 223 := by norm_num
private theorem prime_nonG_229 : Nat.Prime 229 := by norm_num
private theorem prime_nonG_233 : Nat.Prime 233 := by norm_num
private theorem prime_nonG_239 : Nat.Prime 239 := by norm_num
private theorem prime_nonG_251 : Nat.Prime 251 := by norm_num
private theorem prime_nonG_269 : Nat.Prime 269 := by norm_num
private theorem prime_nonG_271 : Nat.Prime 271 := by norm_num
private theorem prime_nonG_277 : Nat.Prime 277 := by norm_num
private theorem prime_nonG_281 : Nat.Prime 281 := by norm_num
private theorem prime_nonG_283 : Nat.Prime 283 := by norm_num
private theorem prime_nonG_293 : Nat.Prime 293 := by norm_num
private theorem prime_nonG_307 : Nat.Prime 307 := by norm_num
private theorem prime_nonG_311 : Nat.Prime 311 := by norm_num
private theorem prime_nonG_313 : Nat.Prime 313 := by norm_num
private theorem prime_nonG_317 : Nat.Prime 317 := by norm_num
private theorem prime_nonG_347 : Nat.Prime 347 := by norm_num
private theorem prime_nonG_353 : Nat.Prime 353 := by norm_num
private theorem prime_nonG_359 : Nat.Prime 359 := by norm_num
private theorem prime_nonG_373 : Nat.Prime 373 := by norm_num
private theorem prime_nonG_379 : Nat.Prime 379 := by norm_num
private theorem prime_nonG_383 : Nat.Prime 383 := by norm_num
private theorem prime_nonG_397 : Nat.Prime 397 := by norm_num
private theorem prime_nonG_409 : Nat.Prime 409 := by norm_num
private theorem prime_nonG_419 : Nat.Prime 419 := by norm_num
private theorem prime_nonG_433 : Nat.Prime 433 := by norm_num
private theorem prime_nonG_439 : Nat.Prime 439 := by norm_num
private theorem prime_nonG_443 : Nat.Prime 443 := by norm_num
private theorem prime_nonG_461 : Nat.Prime 461 := by norm_num
private theorem prime_nonG_463 : Nat.Prime 463 := by norm_num
private theorem prime_nonG_487 : Nat.Prime 487 := by norm_num
private theorem prime_nonG_503 : Nat.Prime 503 := by norm_num
private theorem prime_nonG_521 : Nat.Prime 521 := by norm_num
private theorem prime_nonG_541 : Nat.Prime 541 := by norm_num
private theorem prime_nonG_557 : Nat.Prime 557 := by norm_num
private theorem prime_nonG_563 : Nat.Prime 563 := by norm_num
private theorem prime_nonG_569 : Nat.Prime 569 := by norm_num
private theorem prime_nonG_571 : Nat.Prime 571 := by norm_num
private theorem prime_nonG_577 : Nat.Prime 577 := by norm_num
private theorem prime_nonG_599 : Nat.Prime 599 := by norm_num
private theorem prime_nonG_617 : Nat.Prime 617 := by norm_num
private theorem prime_nonG_631 : Nat.Prime 631 := by norm_num
private theorem prime_nonG_643 : Nat.Prime 643 := by norm_num
private theorem prime_nonG_727 : Nat.Prime 727 := by norm_num
private theorem prime_nonG_739 : Nat.Prime 739 := by norm_num
private theorem prime_nonG_751 : Nat.Prime 751 := by norm_num
private theorem prime_nonG_761 : Nat.Prime 761 := by norm_num
private theorem prime_nonG_769 : Nat.Prime 769 := by norm_num
private theorem prime_nonG_809 : Nat.Prime 809 := by norm_num
private theorem prime_nonG_821 : Nat.Prime 821 := by norm_num
private theorem prime_nonG_877 : Nat.Prime 877 := by norm_num
private theorem prime_nonG_881 : Nat.Prime 881 := by norm_num
private theorem prime_nonG_907 : Nat.Prime 907 := by norm_num
private theorem prime_nonG_919 : Nat.Prime 919 := by norm_num
private theorem prime_nonG_929 : Nat.Prime 929 := by norm_num
private theorem prime_nonG_991 : Nat.Prime 991 := by norm_num
private theorem prime_nonG_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_nonG_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_nonG_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_nonG_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_nonG_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_nonG_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_nonG_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_nonG_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_nonG_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_nonG_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_nonG_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_nonG_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_nonG_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_nonG_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_nonG_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_nonG_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_nonG_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_nonG_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_nonG_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_nonG_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_nonG_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_nonG_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_nonG_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_nonG_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_nonG_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_nonG_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_nonG_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_nonG_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_nonG_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_nonG_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_nonG_2609 : Nat.Prime 2609 := by norm_num
private theorem prime_nonG_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_nonG_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_nonG_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_nonG_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_nonG_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_nonG_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_nonG_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_nonG_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_nonG_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_nonG_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_nonG_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_nonG_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_nonG_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_nonG_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_nonG_3613 : Nat.Prime 3613 := by norm_num
private theorem prime_nonG_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_nonG_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_nonG_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_nonG_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_nonG_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_nonG_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_nonG_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_nonG_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_nonG_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_nonG_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_nonG_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_nonG_5101 : Nat.Prime 5101 := by norm_num
private theorem prime_nonG_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_nonG_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_nonG_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_nonG_5851 : Nat.Prime 5851 := by norm_num
private theorem prime_nonG_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_nonG_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_nonG_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_nonG_6857 : Nat.Prime 6857 := by norm_num
private theorem prime_nonG_6949 : Nat.Prime 6949 := by norm_num
private theorem prime_nonG_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_nonG_7321 : Nat.Prime 7321 := by norm_num
private theorem prime_nonG_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_nonG_7853 : Nat.Prime 7853 := by norm_num
private theorem prime_nonG_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_nonG_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_nonG_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_nonG_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_nonG_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_nonG_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_nonG_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_nonG_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_nonG_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_nonG_9397 : Nat.Prime 9397 := by norm_num
private theorem prime_nonG_10169 : Nat.Prime 10169 := by norm_num
private theorem prime_nonG_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_nonG_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_nonG_11177 : Nat.Prime 11177 := by norm_num
private theorem prime_nonG_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_nonG_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_nonG_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_nonG_12487 : Nat.Prime 12487 := by norm_num
private theorem prime_nonG_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_nonG_12941 : Nat.Prime 12941 := by norm_num
private theorem prime_nonG_13397 : Nat.Prime 13397 := by norm_num
private theorem prime_nonG_13751 : Nat.Prime 13751 := by norm_num
private theorem prime_nonG_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_nonG_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_nonG_15107 : Nat.Prime 15107 := by norm_num
private theorem prime_nonG_15401 : Nat.Prime 15401 := by norm_num
private theorem prime_nonG_16189 : Nat.Prime 16189 := by norm_num
private theorem prime_nonG_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_nonG_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_nonG_17389 : Nat.Prime 17389 := by norm_num
private theorem prime_nonG_17683 : Nat.Prime 17683 := by norm_num
private theorem prime_nonG_17929 : Nat.Prime 17929 := by norm_num
private theorem prime_nonG_18077 : Nat.Prime 18077 := by norm_num
private theorem prime_nonG_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_nonG_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_nonG_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_nonG_20231 : Nat.Prime 20231 := by norm_num
private theorem prime_nonG_20719 : Nat.Prime 20719 := by norm_num
private theorem prime_nonG_21011 : Nat.Prime 21011 := by norm_num
private theorem prime_nonG_21649 : Nat.Prime 21649 := by norm_num
private theorem prime_nonG_22543 : Nat.Prime 22543 := by norm_num
private theorem prime_nonG_22613 : Nat.Prime 22613 := by norm_num
private theorem prime_nonG_23539 : Nat.Prime 23539 := by norm_num
private theorem prime_nonG_24593 : Nat.Prime 24593 := by norm_num
private theorem prime_nonG_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_nonG_26539 : Nat.Prime 26539 := by norm_num
private theorem prime_nonG_26921 : Nat.Prime 26921 := by norm_num
private theorem prime_nonG_26959 : Nat.Prime 26959 := by norm_num
private theorem prime_nonG_28097 : Nat.Prime 28097 := by norm_num
private theorem prime_nonG_28123 : Nat.Prime 28123 := by norm_num
private theorem prime_nonG_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_nonG_28867 : Nat.Prime 28867 := by norm_num
private theorem prime_nonG_29179 : Nat.Prime 29179 := by norm_num
private theorem prime_nonG_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_nonG_34057 : Nat.Prime 34057 := by norm_num
private theorem prime_nonG_34147 : Nat.Prime 34147 := by norm_num
private theorem prime_nonG_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_nonG_34847 : Nat.Prime 34847 := by norm_num
private theorem prime_nonG_34913 : Nat.Prime 34913 := by norm_num
private theorem prime_nonG_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_nonG_36017 : Nat.Prime 36017 := by norm_num
private theorem prime_nonG_36749 : Nat.Prime 36749 := by norm_num
private theorem prime_nonG_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_nonG_37313 : Nat.Prime 37313 := by norm_num
private theorem prime_nonG_39989 : Nat.Prime 39989 := by norm_num
private theorem prime_nonG_41627 : Nat.Prime 41627 := by norm_num
private theorem prime_nonG_41851 : Nat.Prime 41851 := by norm_num
private theorem prime_nonG_43189 : Nat.Prime 43189 := by norm_num
private theorem prime_nonG_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_nonG_49811 : Nat.Prime 49811 := by norm_num
private theorem prime_nonG_52859 : Nat.Prime 52859 := by norm_num
private theorem prime_nonG_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_nonG_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_nonG_55807 : Nat.Prime 55807 := by norm_num
private theorem prime_nonG_56453 : Nat.Prime 56453 := by norm_num
private theorem prime_nonG_58229 : Nat.Prime 58229 := by norm_num
private theorem prime_nonG_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_nonG_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_nonG_63493 : Nat.Prime 63493 := by norm_num
private theorem prime_nonG_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_nonG_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_nonG_76943 : Nat.Prime 76943 := by norm_num
private theorem prime_nonG_79181 : Nat.Prime 79181 := by norm_num
private theorem prime_nonG_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_nonG_82529 : Nat.Prime 82529 := by norm_num
private theorem prime_nonG_86843 : Nat.Prime 86843 := by norm_num
private theorem prime_nonG_86851 : Nat.Prime 86851 := by norm_num
private theorem prime_nonG_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_nonG_96293 : Nat.Prime 96293 := by norm_num
private theorem prime_nonG_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_nonG_100847 : Nat.Prime 100847 := by norm_num
private theorem prime_nonG_105373 : Nat.Prime 105373 := by norm_num
private theorem prime_nonG_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_nonG_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_nonG_114883 : Nat.Prime 114883 := by norm_num
private theorem prime_nonG_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_nonG_121621 : Nat.Prime 121621 := by norm_num
private theorem prime_nonG_122663 : Nat.Prime 122663 := by norm_num
private theorem prime_nonG_140659 : Nat.Prime 140659 := by norm_num
private theorem prime_nonG_152441 : Nat.Prime 152441 := by norm_num
private theorem prime_nonG_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_nonG_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_nonG_161461 : Nat.Prime 161461 := by norm_num
private theorem prime_nonG_170327 : Nat.Prime 170327 := by norm_num
private theorem prime_nonG_171877 : Nat.Prime 171877 := by norm_num
private theorem prime_nonG_173827 : Nat.Prime 173827 := by norm_num
private theorem prime_nonG_175691 : Nat.Prime 175691 := by norm_num
private theorem prime_nonG_177887 : Nat.Prime 177887 := by norm_num
private theorem prime_nonG_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_nonG_186869 : Nat.Prime 186869 := by norm_num
private theorem prime_nonG_189067 : Nat.Prime 189067 := by norm_num
private theorem prime_nonG_192263 : Nat.Prime 192263 := by norm_num
private theorem prime_nonG_192883 : Nat.Prime 192883 := by norm_num
private theorem prime_nonG_198997 : Nat.Prime 198997 := by norm_num
private theorem prime_nonG_204749 : Nat.Prime 204749 := by norm_num
private theorem prime_nonG_210739 : Nat.Prime 210739 := by norm_num
private theorem prime_nonG_212453 : Nat.Prime 212453 := by norm_num
private theorem prime_nonG_215447 : Nat.Prime 215447 := by norm_num
private theorem prime_nonG_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_nonG_276707 : Nat.Prime 276707 := by norm_num
private theorem prime_nonG_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_nonG_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_nonG_295441 : Nat.Prime 295441 := by norm_num
private theorem prime_nonG_320317 : Nat.Prime 320317 := by norm_num
private theorem prime_nonG_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_nonG_339907 : Nat.Prime 339907 := by norm_num
private theorem prime_nonG_357347 : Nat.Prime 357347 := by norm_num
private theorem prime_nonG_373721 : Nat.Prime 373721 := by norm_num
private theorem prime_nonG_394153 : Nat.Prime 394153 := by norm_num
private theorem prime_nonG_401987 : Nat.Prime 401987 := by norm_num
private theorem prime_nonG_405497 : Nat.Prime 405497 := by norm_num
private theorem prime_nonG_418069 : Nat.Prime 418069 := by norm_num
private theorem prime_nonG_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_nonG_441101 : Nat.Prime 441101 := by norm_num
private theorem prime_nonG_441971 : Nat.Prime 441971 := by norm_num
private theorem prime_nonG_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_nonG_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_nonG_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_nonG_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_nonG_572993 : Nat.Prime 572993 := by norm_num
private theorem prime_nonG_616277 : Nat.Prime 616277 := by norm_num
private theorem prime_nonG_619537 : Nat.Prime 619537 := by norm_num
private theorem prime_nonG_622367 : Nat.Prime 622367 := by norm_num
private theorem prime_nonG_627547 : Nat.Prime 627547 := by norm_num
private theorem prime_nonG_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_nonG_646619 : Nat.Prime 646619 := by norm_num
private theorem prime_nonG_668867 : Nat.Prime 668867 := by norm_num
private theorem prime_nonG_686731 : Nat.Prime 686731 := by norm_num
private theorem prime_nonG_704321 : Nat.Prime 704321 := by norm_num
private theorem prime_nonG_706883 : Nat.Prime 706883 := by norm_num
private theorem prime_nonG_722317 : Nat.Prime 722317 := by norm_num
private theorem prime_nonG_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_nonG_842077 : Nat.Prime 842077 := by norm_num
private theorem prime_nonG_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_nonG_925079 : Nat.Prime 925079 := by norm_num
private theorem prime_nonG_953221 : Nat.Prime 953221 := by norm_num
private theorem prime_nonG_1015907 : Nat.Prime 1015907 := by norm_num
private theorem prime_nonG_1114549 : Nat.Prime 1114549 := by norm_num
private theorem prime_nonG_1132697 : Nat.Prime 1132697 := by norm_num
private theorem prime_nonG_1176533 : Nat.Prime 1176533 := by norm_num
private theorem prime_nonG_1192327 : Nat.Prime 1192327 := by norm_num
private theorem prime_nonG_1244879 : Nat.Prime 1244879 := by norm_num
private theorem prime_nonG_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_nonG_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_nonG_1644991 : Nat.Prime 1644991 := by norm_num
private theorem prime_nonG_1652843 : Nat.Prime 1652843 := by norm_num
private theorem prime_nonG_1673377 : Nat.Prime 1673377 := by norm_num
private theorem prime_nonG_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_nonG_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_nonG_1935133 : Nat.Prime 1935133 := by norm_num
private theorem prime_nonG_2066201 : Nat.Prime 2066201 := by norm_num
private theorem prime_nonG_2103139 : Nat.Prime 2103139 := by norm_num
private theorem prime_nonG_2202311 : Nat.Prime 2202311 := by norm_num
private theorem prime_nonG_2284423 : Nat.Prime 2284423 := by norm_num
private theorem prime_nonG_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_nonG_2496379 : Nat.Prime 2496379 := by norm_num
private theorem prime_nonG_2632859 : Nat.Prime 2632859 := by norm_num
private theorem prime_nonG_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_nonG_2771233 : Nat.Prime 2771233 := by norm_num
private theorem prime_nonG_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_nonG_3044831 : Nat.Prime 3044831 := by norm_num
private theorem prime_nonG_3081137 : Nat.Prime 3081137 := by norm_num
private theorem prime_nonG_3207943 : Nat.Prime 3207943 := by norm_num
private theorem prime_nonG_3269977 : Nat.Prime 3269977 := by norm_num
private theorem prime_nonG_3363887 : Nat.Prime 3363887 := by norm_num
private theorem prime_nonG_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_nonG_3712717 : Nat.Prime 3712717 := by norm_num
private theorem prime_nonG_4175273 : Nat.Prime 4175273 := by norm_num
private theorem prime_nonG_4242317 : Nat.Prime 4242317 := by norm_num
private theorem prime_nonG_4597709 : Nat.Prime 4597709 := by norm_num
private theorem prime_nonG_4722547 : Nat.Prime 4722547 := by norm_num
private theorem prime_nonG_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_nonG_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_nonG_5054317 : Nat.Prime 5054317 := by norm_num
private theorem prime_nonG_5093789 : Nat.Prime 5093789 := by norm_num
private theorem prime_nonG_5181151 : Nat.Prime 5181151 := by norm_num
private theorem prime_nonG_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_nonG_6307033 : Nat.Prime 6307033 := by norm_num
private theorem prime_nonG_6456001 : Nat.Prime 6456001 := by norm_num
private theorem prime_nonG_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_nonG_7290853 : Nat.Prime 7290853 := by norm_num
private theorem prime_nonG_7316849 : Nat.Prime 7316849 := by norm_num
private theorem prime_nonG_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_nonG_7587443 : Nat.Prime 7587443 := by norm_num
private theorem prime_nonG_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_nonG_7982567 : Nat.Prime 7982567 := by norm_num
private theorem prime_nonG_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_nonG_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_nonG_8917369 : Nat.Prime 8917369 := by norm_num
private theorem prime_nonG_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_nonG_9715439 : Nat.Prime 9715439 := by norm_num
private theorem prime_nonG_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_nonG_11213231 : Nat.Prime 11213231 := by norm_num
private theorem prime_nonG_11537861 : Nat.Prime 11537861 := by norm_num
private theorem prime_nonG_11641387 : Nat.Prime 11641387 := by norm_num
private theorem prime_nonG_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_nonG_12759209 : Nat.Prime 12759209 := by norm_num
private theorem prime_nonG_12829519 : Nat.Prime 12829519 := by norm_num
private theorem prime_nonG_12986333 : Nat.Prime 12986333 := by norm_num
private theorem prime_nonG_13311821 : Nat.Prime 13311821 := by norm_num
private theorem prime_nonG_13470463 : Nat.Prime 13470463 := by norm_num
private theorem prime_nonG_13972271 : Nat.Prime 13972271 := by norm_num
private theorem prime_nonG_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_nonG_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_nonG_16105963 : Nat.Prime 16105963 := by norm_num
private theorem prime_nonG_17010061 : Nat.Prime 17010061 := by norm_num
private theorem prime_nonG_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_nonG_17885311 : Nat.Prime 17885311 := by norm_num
private theorem prime_nonG_19996541 : Nat.Prime 19996541 := by norm_num

private theorem prime_nonG_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_23
      · exact prime_nonG_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_21119159 : Nat.Prime 21119159 := by
  apply lucas_primality 21119159 (43 : ZMod 21119159)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (283, 1), (37313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (283, 1), (37313, 1)] : List FactorBlock).map factorBlockValue).prod = 21119159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_283
      · exact prime_nonG_37313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (43 : ZMod 21119159) ^ 10559579 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (43 : ZMod 21119159) ^ 74626 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (43 : ZMod 21119159) ^ 566 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_26126021 : Nat.Prime 26126021 := by
  apply lucas_primality 26126021 (3 : ZMod 26126021)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod = 26126021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_41
      · exact prime_nonG_151
      · exact prime_nonG_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26126021) ^ 13063010 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 5225204 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 637220 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 173020 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 123820 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_32439761 : Nat.Prime 32439761 := by
  apply lucas_primality 32439761 (3 : ZMod 32439761)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (405497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (405497, 1)] : List FactorBlock).map factorBlockValue).prod = 32439761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_405497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32439761) ^ 16219880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32439761) ^ 6487952 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 32439761) ^ 80 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_39415301 : Nat.Prime 39415301 := by
  apply lucas_primality 39415301 (2 : ZMod 39415301)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (394153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (394153, 1)] : List FactorBlock).map factorBlockValue).prod = 39415301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_394153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39415301) ^ 19707650 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 39415301) ^ 7883060 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 39415301) ^ 100 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_40161049 : Nat.Prime 40161049 := by
  apply lucas_primality 40161049 (7 : ZMod 40161049)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (1673377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (1673377, 1)] : List FactorBlock).map factorBlockValue).prod = 40161049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_1673377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 40161049) ^ 20080524 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 40161049) ^ 13387016 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 40161049) ^ 24 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_44619727 : Nat.Prime 44619727 := by
  apply lucas_primality 44619727 (5 : ZMod 44619727)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (31, 1), (41, 1), (5851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (31, 1), (41, 1), (5851, 1)] : List FactorBlock).map factorBlockValue).prod = 44619727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_31
      · exact prime_nonG_41
      · exact prime_nonG_5851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44619727) ^ 22309863 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 44619727) ^ 14873242 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 44619727) ^ 1439346 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 44619727) ^ 1088286 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 44619727) ^ 7626 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_63388891 : Nat.Prime 63388891 := by
  apply lucas_primality 63388891 (2 : ZMod 63388891)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod = 63388891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_704321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63388891) ^ 31694445 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 21129630 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 12677778 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 90 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_87498511 : Nat.Prime 87498511 := by
  apply lucas_primality 87498511 (7 : ZMod 87498511)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (41, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (41, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod = 87498511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_29
      · exact prime_nonG_41
      · exact prime_nonG_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 87498511) ^ 43749255 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 29166170 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 17499702 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 7954410 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 3017190 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 2134110 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 87498511) ^ 392370 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_91688203 : Nat.Prime 91688203 := by
  apply lucas_primality 91688203 (3 : ZMod 91688203)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5093789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5093789, 1)] : List FactorBlock).map factorBlockValue).prod = 91688203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5093789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 91688203) ^ 45844101 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 91688203) ^ 30562734 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 91688203) ^ 18 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_160512643 : Nat.Prime 160512643 := by
  apply lucas_primality 160512643 (2 : ZMod 160512643)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod = 160512643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_8917369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160512643) ^ 80256321 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 53504214 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 18 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_181957939 : Nat.Prime 181957939 := by
  apply lucas_primality 181957939 (2 : ZMod 181957939)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod = 181957939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_383
      · exact prime_nonG_79181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181957939) ^ 90978969 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 60652646 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 475086 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 2298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_282045737 : Nat.Prime 282045737 := by
  apply lucas_primality 282045737 (3 : ZMod 282045737)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod = 282045737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_97
      · exact prime_nonG_137
      · exact prime_nonG_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 282045737) ^ 141022868 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 40292248 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2907688 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2058728 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 744184 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_321935599 : Nat.Prime 321935599 := by
  apply lucas_primality 321935599 (6 : ZMod 321935599)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod = 321935599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_17885311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 321935599) ^ 160967799 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 321935599) ^ 107311866 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 321935599) ^ 18 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_374221343 : Nat.Prime 374221343 := by
  apply lucas_primality 374221343 (5 : ZMod 374221343)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17010061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17010061, 1)] : List FactorBlock).map factorBlockValue).prod = 374221343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_17010061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 374221343) ^ 187110671 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 374221343) ^ 34020122 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 374221343) ^ 22 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_404727353 : Nat.Prime 404727353 := by
  apply lucas_primality 404727353 (3 : ZMod 404727353)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (43, 1), (1176533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (43, 1), (1176533, 1)] : List FactorBlock).map factorBlockValue).prod = 404727353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_43
      · exact prime_nonG_1176533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 404727353) ^ 202363676 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 404727353) ^ 9412264 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 404727353) ^ 344 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_448035727 : Nat.Prime 448035727 := by
  apply lucas_primality 448035727 (5 : ZMod 448035727)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3691, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3691, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod = 448035727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_3691
      · exact prime_nonG_20231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 448035727) ^ 224017863 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 448035727) ^ 149345242 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 448035727) ^ 121386 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 448035727) ^ 22146 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_464968781 : Nat.Prime 464968781 := by
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_103
      · exact prime_nonG_131
      · exact prime_nonG_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 464968781) ^ 232484390 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 92993756 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 4514260 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 3549380 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 269860 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_754168979 : Nat.Prime 754168979 := by
  apply lucas_primality 754168979 (2 : ZMod 754168979)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1009, 1), (373721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1009, 1), (373721, 1)] : List FactorBlock).map factorBlockValue).prod = 754168979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1009
      · exact prime_nonG_373721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 754168979) ^ 377084489 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 754168979) ^ 747442 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 754168979) ^ 2018 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_979501163 : Nat.Prime 979501163 := by
  apply lucas_primality 979501163 (2 : ZMod 979501163)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod = 979501163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_53
      · exact prime_nonG_1787
      · exact prime_nonG_5171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 979501163) ^ 489750581 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 18481154 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 548126 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 189422 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_29
      · exact prime_nonG_113
      · exact prime_nonG_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1314491287 : Nat.Prime 1314491287 := by
  apply lucas_primality 1314491287 (5 : ZMod 1314491287)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1907, 1), (114883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1907, 1), (114883, 1)] : List FactorBlock).map factorBlockValue).prod = 1314491287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_1907
      · exact prime_nonG_114883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1314491287) ^ 657245643 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1314491287) ^ 438163762 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1314491287) ^ 689298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1314491287) ^ 11442 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_17
      · exact prime_nonG_79
      · exact prime_nonG_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2076644077 : Nat.Prime 2076644077 := by
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2076644077) ^ 1038322038 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 692214692 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 159741852 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 156 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_239
      · exact prime_nonG_283
      · exact prime_nonG_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4054368629 : Nat.Prime 4054368629 := by
  apply lucas_primality 4054368629 (2 : ZMod 4054368629)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (157, 1), (6456001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (157, 1), (6456001, 1)] : List FactorBlock).map factorBlockValue).prod = 4054368629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_157
      · exact prime_nonG_6456001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4054368629) ^ 2027184314 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4054368629) ^ 25824004 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4054368629) ^ 628 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_30500077 : Nat.Prime 30500077 := by
  apply lucas_primality 30500077 (5 : ZMod 30500077)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (157, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (157, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod = 30500077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_157
      · exact prime_nonG_16189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30500077) ^ 15250038 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 10166692 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 194268 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 1884 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4209010627 : Nat.Prime 4209010627 := by
  apply lucas_primality 4209010627 (2 : ZMod 4209010627)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (30500077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (30500077, 1)] : List FactorBlock).map factorBlockValue).prod = 4209010627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_23
      · exact prime_nonG_30500077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4209010627) ^ 2104505313 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 1403003542 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 183000462 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 138 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4946199949 : Nat.Prime 4946199949 := by
  apply lucas_primality 4946199949 (2 : ZMod 4946199949)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (71, 1), (1935133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (71, 1), (1935133, 1)] : List FactorBlock).map factorBlockValue).prod = 4946199949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_71
      · exact prime_nonG_1935133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4946199949) ^ 2473099974 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4946199949) ^ 1648733316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4946199949) ^ 69664788 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4946199949) ^ 2556 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2491021289 : Nat.Prime 2491021289 := by
  apply lucas_primality 2491021289 (3 : ZMod 2491021289)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod = 2491021289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_17
      · exact prime_nonG_433
      · exact prime_nonG_6043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2491021289) ^ 1245510644 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 355860184 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 146530664 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 5752936 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 412216 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4982042579 : Nat.Prime 4982042579 := by
  apply lucas_primality 4982042579 (2 : ZMod 4982042579)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod = 4982042579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_2491021289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4982042579) ^ 2491021289 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982042579) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_5489884663 : Nat.Prime 5489884663 := by
  apply lucas_primality 5489884663 (3 : ZMod 5489884663)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (163, 1), (295441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (163, 1), (295441, 1)] : List FactorBlock).map factorBlockValue).prod = 5489884663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_163
      · exact prime_nonG_295441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5489884663) ^ 2744942331 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5489884663) ^ 1829961554 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5489884663) ^ 288941298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5489884663) ^ 33680274 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5489884663) ^ 18582 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_961954627 : Nat.Prime 961954627 := by
  apply lucas_primality 961954627 (2 : ZMod 961954627)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod = 961954627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_97
      · exact prime_nonG_1652843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 961954627) ^ 480977313 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 320651542 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 9917058 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 582 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_5771727763 : Nat.Prime 5771727763 := by
  apply lucas_primality 5771727763 (3 : ZMod 5771727763)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod = 5771727763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_961954627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5771727763) ^ 2885863881 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 1923909254 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 6 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_89
      · exact prime_nonG_223
      · exact prime_nonG_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_6442882141 : Nat.Prime 6442882141 := by
  apply lucas_primality 6442882141 (7 : ZMod 6442882141)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (67, 2), (1259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (67, 2), (1259, 1)] : List FactorBlock).map factorBlockValue).prod = 6442882141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_19
      · exact prime_nonG_67
      · exact prime_nonG_1259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6442882141) ^ 3221441070 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6442882141) ^ 2147627380 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6442882141) ^ 1288576428 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6442882141) ^ 339099060 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6442882141) ^ 96162420 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6442882141) ^ 5117460 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_1483
      · exact prime_nonG_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_73
      · exact prime_nonG_397
      · exact prime_nonG_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_235217063 : Nat.Prime 235217063 := by
  apply lucas_primality 235217063 (5 : ZMod 235217063)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149, 1), (541, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149, 1), (541, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod = 235217063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_149
      · exact prime_nonG_541
      · exact prime_nonG_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 235217063) ^ 117608531 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 235217063) ^ 1578638 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 235217063) ^ 434782 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 235217063) ^ 161218 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_9879116647 : Nat.Prime 9879116647 := by
  apply lucas_primality 9879116647 (3 : ZMod 9879116647)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (235217063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (235217063, 1)] : List FactorBlock).map factorBlockValue).prod = 9879116647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_235217063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9879116647) ^ 4939558323 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9879116647) ^ 3293038882 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9879116647) ^ 1411302378 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9879116647) ^ 42 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_10925593411 : Nat.Prime 10925593411 := by
  apply lucas_primality 10925593411 (2 : ZMod 10925593411)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (2969, 1), (122663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (2969, 1), (122663, 1)] : List FactorBlock).map factorBlockValue).prod = 10925593411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_2969
      · exact prime_nonG_122663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10925593411) ^ 5462796705 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10925593411) ^ 3641864470 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10925593411) ^ 2185118682 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10925593411) ^ 3679890 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10925593411) ^ 89070 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_23
      · exact prime_nonG_47
      · exact prime_nonG_59
      · exact prime_nonG_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_13493024417 : Nat.Prime 13493024417 := by
  apply lucas_primality 13493024417 (3 : ZMod 13493024417)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (29, 1), (229, 1), (63493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (29, 1), (229, 1), (63493, 1)] : List FactorBlock).map factorBlockValue).prod = 13493024417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_29
      · exact prime_nonG_229
      · exact prime_nonG_63493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13493024417) ^ 6746512208 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13493024417) ^ 465276704 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13493024417) ^ 58921504 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13493024417) ^ 212512 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_106222201 : Nat.Prime 106222201 := by
  apply lucas_primality 106222201 (22 : ZMod 106222201)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (7, 2), (3613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (7, 2), (3613, 1)] : List FactorBlock).map factorBlockValue).prod = 106222201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_3613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 106222201) ^ 53111100 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (22 : ZMod 106222201) ^ 35407400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (22 : ZMod 106222201) ^ 21244440 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (22 : ZMod 106222201) ^ 15174600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (22 : ZMod 106222201) ^ 29400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1699555217 : Nat.Prime 1699555217 := by
  apply lucas_primality 1699555217 (3 : ZMod 1699555217)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (106222201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (106222201, 1)] : List FactorBlock).map factorBlockValue).prod = 1699555217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_106222201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1699555217) ^ 849777608 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1699555217) ^ 16 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_13596441737 : Nat.Prime 13596441737 := by
  apply lucas_primality 13596441737 (3 : ZMod 13596441737)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1699555217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1699555217, 1)] : List FactorBlock).map factorBlockValue).prod = 13596441737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1699555217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13596441737) ^ 6798220868 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13596441737) ^ 8 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_17
      · exact prime_nonG_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_71
      · exact prime_nonG_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_42394621 : Nat.Prime 42394621 := by
  apply lucas_primality 42394621 (2 : ZMod 42394621)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (167, 1), (4231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (167, 1), (4231, 1)] : List FactorBlock).map factorBlockValue).prod = 42394621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_167
      · exact prime_nonG_4231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42394621) ^ 21197310 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 42394621) ^ 14131540 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 42394621) ^ 8478924 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 42394621) ^ 253860 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 42394621) ^ 10020 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_40698836161 : Nat.Prime 40698836161 := by
  apply lucas_primality 40698836161 (59 : ZMod 40698836161)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 1), (42394621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 1), (42394621, 1)] : List FactorBlock).map factorBlockValue).prod = 40698836161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_42394621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (59 : ZMod 40698836161) ^ 20349418080 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (59 : ZMod 40698836161) ^ 13566278720 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (59 : ZMod 40698836161) ^ 8139767232 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (59 : ZMod 40698836161) ^ 960 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_51564258659 : Nat.Prime 51564258659 := by
  apply lucas_primality 51564258659 (6 : ZMod 51564258659)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 2), (43, 1), (631, 1), (7853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 2), (43, 1), (631, 1), (7853, 1)] : List FactorBlock).map factorBlockValue).prod = 51564258659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_43
      · exact prime_nonG_631
      · exact prime_nonG_7853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51564258659) ^ 25782129329 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 4687659878 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 1199168806 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 81718318 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 6566186 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_9184016489 : Nat.Prime 9184016489 := by
  apply lucas_primality 9184016489 (3 : ZMod 9184016489)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (109, 1), (619537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (109, 1), (619537, 1)] : List FactorBlock).map factorBlockValue).prod = 9184016489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_17
      · exact prime_nonG_109
      · exact prime_nonG_619537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9184016489) ^ 4592008244 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9184016489) ^ 540236264 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9184016489) ^ 84257032 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9184016489) ^ 14824 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_73472131913 : Nat.Prime 73472131913 := by
  apply lucas_primality 73472131913 (3 : ZMod 73472131913)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (9184016489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (9184016489, 1)] : List FactorBlock).map factorBlockValue).prod = 73472131913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_9184016489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73472131913) ^ 36736065956 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 73472131913) ^ 8 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_47288273 : Nat.Prime 47288273 := by
  apply lucas_primality 47288273 (3 : ZMod 47288273)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (71, 1), (41627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (71, 1), (41627, 1)] : List FactorBlock).map factorBlockValue).prod = 47288273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_71
      · exact prime_nonG_41627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47288273) ^ 23644136 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47288273) ^ 666032 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47288273) ^ 1136 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_77269038083 : Nat.Prime 77269038083 := by
  apply lucas_primality 77269038083 (2 : ZMod 77269038083)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (43, 1), (47288273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (43, 1), (47288273, 1)] : List FactorBlock).map factorBlockValue).prod = 77269038083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_19
      · exact prime_nonG_43
      · exact prime_nonG_47288273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77269038083) ^ 38634519041 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77269038083) ^ 4066791478 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77269038083) ^ 1796954374 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77269038083) ^ 1634 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_103524837131 : Nat.Prime 103524837131 := by
  apply lucas_primality 103524837131 (2 : ZMod 103524837131)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (13, 1), (29, 1), (2496379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (13, 1), (29, 1), (2496379, 1)] : List FactorBlock).map factorBlockValue).prod = 103524837131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_29
      · exact prime_nonG_2496379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103524837131) ^ 51762418565 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103524837131) ^ 20704967426 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103524837131) ^ 9411348830 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103524837131) ^ 7963449010 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103524837131) ^ 3569821970 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103524837131) ^ 41470 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_152270997001 : Nat.Prime 152270997001 := by
  apply lucas_primality 152270997001 (11 : ZMod 152270997001)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 3), (19, 1), (149, 1), (17929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 3), (19, 1), (149, 1), (17929, 1)] : List FactorBlock).map factorBlockValue).prod = 152270997001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_19
      · exact prime_nonG_149
      · exact prime_nonG_17929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 152270997001) ^ 76135498500 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 152270997001) ^ 50756999000 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 152270997001) ^ 30454199400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 152270997001) ^ 8014263000 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 152270997001) ^ 1021953000 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 152270997001) ^ 8493000 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_173711112271 : Nat.Prime 173711112271 := by
  apply lucas_primality 173711112271 (6 : ZMod 173711112271)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (18077, 1), (320317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (18077, 1), (320317, 1)] : List FactorBlock).map factorBlockValue).prod = 173711112271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_18077
      · exact prime_nonG_320317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 173711112271) ^ 86855556135 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173711112271) ^ 57903704090 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173711112271) ^ 34742222454 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173711112271) ^ 9609510 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 173711112271) ^ 542310 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_183325663427 : Nat.Prime 183325663427 := by
  apply lucas_primality 183325663427 (2 : ZMod 183325663427)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod = 183325663427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1831
      · exact prime_nonG_5479
      · exact prime_nonG_9137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183325663427) ^ 91662831713 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 100123246 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 33459694 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 20064098 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_149
      · exact prime_nonG_1429
      · exact prime_nonG_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_400597142329 : Nat.Prime 400597142329 := by
  apply lucas_primality 400597142329 (11 : ZMod 400597142329)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod = 400597142329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_17
      · exact prime_nonG_41
      · exact prime_nonG_7982567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 400597142329) ^ 200298571164 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 133532380776 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 23564537784 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 9770662008 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 50184 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_560911155227 : Nat.Prime 560911155227 := by
  apply lucas_primality 560911155227 (2 : ZMod 560911155227)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (28867, 1), (9715439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (28867, 1), (9715439, 1)] : List FactorBlock).map factorBlockValue).prod = 560911155227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_28867
      · exact prime_nonG_9715439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 560911155227) ^ 280455577613 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 560911155227) ^ 19430878 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 560911155227) ^ 57734 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_43554465319 : Nat.Prime 43554465319 := by
  apply lucas_primality 43554465319 (6 : ZMod 43554465319)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (13, 1), (1847, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (13, 1), (1847, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod = 43554465319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_13
      · exact prime_nonG_1847
      · exact prime_nonG_43189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 43554465319) ^ 21777232659 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 43554465319) ^ 14518155106 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 43554465319) ^ 6222066474 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 43554465319) ^ 3350343486 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 43554465319) ^ 23581194 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 43554465319) ^ 1008462 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_783980375743 : Nat.Prime 783980375743 := by
  apply lucas_primality 783980375743 (3 : ZMod 783980375743)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (43554465319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (43554465319, 1)] : List FactorBlock).map factorBlockValue).prod = 783980375743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_43554465319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 783980375743) ^ 391990187871 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 783980375743) ^ 261326791914 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 783980375743) ^ 18 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_29
      · exact prime_nonG_53
      · exact prime_nonG_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_13
      · exact prime_nonG_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3078901753 : Nat.Prime 3078901753 := by
  apply lucas_primality 3078901753 (5 : ZMod 3078901753)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (359, 1), (357347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (359, 1), (357347, 1)] : List FactorBlock).map factorBlockValue).prod = 3078901753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_359
      · exact prime_nonG_357347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3078901753) ^ 1539450876 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3078901753) ^ 1026300584 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3078901753) ^ 8576328 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3078901753) ^ 8616 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1139193648611 : Nat.Prime 1139193648611 := by
  apply lucas_primality 1139193648611 (6 : ZMod 1139193648611)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 1), (3078901753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 1), (3078901753, 1)] : List FactorBlock).map factorBlockValue).prod = 1139193648611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_37
      · exact prime_nonG_3078901753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1139193648611) ^ 569596824305 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1139193648611) ^ 227838729722 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1139193648611) ^ 30789017530 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1139193648611) ^ 370 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2278387297223 : Nat.Prime 2278387297223 := by
  apply lucas_primality 2278387297223 (5 : ZMod 2278387297223)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1139193648611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1139193648611, 1)] : List FactorBlock).map factorBlockValue).prod = 2278387297223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1139193648611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2278387297223) ^ 1139193648611 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2278387297223) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_24602178841 : Nat.Prime 24602178841 := by
  apply lucas_primality 24602178841 (13 : ZMod 24602178841)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (181, 1), (1132697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (181, 1), (1132697, 1)] : List FactorBlock).map factorBlockValue).prod = 24602178841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_181
      · exact prime_nonG_1132697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24602178841) ^ 12301089420 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 24602178841) ^ 8200726280 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 24602178841) ^ 4920435768 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 24602178841) ^ 135923640 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 24602178841) ^ 21720 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2755444030193 : Nat.Prime 2755444030193 := by
  apply lucas_primality 2755444030193 (3 : ZMod 2755444030193)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (24602178841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (24602178841, 1)] : List FactorBlock).map factorBlockValue).prod = 2755444030193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_24602178841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2755444030193) ^ 1377722015096 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755444030193) ^ 393634861456 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755444030193) ^ 112 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_53221916653 : Nat.Prime 53221916653 := by
  apply lucas_primality 53221916653 (6 : ZMod 53221916653)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 3), (646619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 3), (646619, 1)] : List FactorBlock).map factorBlockValue).prod = 53221916653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_646619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 53221916653) ^ 26610958326 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53221916653) ^ 17740638884 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53221916653) ^ 2801153508 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 53221916653) ^ 82308 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_212887666613 : Nat.Prime 212887666613 := by
  apply lucas_primality 212887666613 (2 : ZMod 212887666613)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (53221916653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (53221916653, 1)] : List FactorBlock).map factorBlockValue).prod = 212887666613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_53221916653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 212887666613) ^ 106443833306 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 212887666613) ^ 4 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2980427332583 : Nat.Prime 2980427332583 := by
  apply lucas_primality 2980427332583 (5 : ZMod 2980427332583)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (212887666613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (212887666613, 1)] : List FactorBlock).map factorBlockValue).prod = 2980427332583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_212887666613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2980427332583) ^ 1490213666291 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2980427332583) ^ 425775333226 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2980427332583) ^ 14 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_7476772742657 : Nat.Prime 7476772742657 := by
  apply lucas_primality 7476772742657 (3 : ZMod 7476772742657)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (7, 1), (307, 1), (991, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (7, 1), (307, 1), (991, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod = 7476772742657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_307
      · exact prime_nonG_991
      · exact prime_nonG_6857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7476772742657) ^ 3738386371328 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7476772742657) ^ 1068110391808 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7476772742657) ^ 24354308608 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7476772742657) ^ 7544674816 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7476772742657) ^ 1090385408 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_9281
      · exact prime_nonG_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_18596513447881 : Nat.Prime 18596513447881 := by
  apply lucas_primality 18596513447881 (13 : ZMod 18596513447881)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod = 18596513447881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_73
      · exact prime_nonG_2939
      · exact prime_nonG_722317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18596513447881) ^ 9298256723940 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6198837815960 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 3719302689576 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 254746759560 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6327496920 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 25745640 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_47
      · exact prime_nonG_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_47
      · exact prime_nonG_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_29
      · exact prime_nonG_34361
      · exact prime_nonG_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_23
      · exact prime_nonG_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_166895539 : Nat.Prime 166895539 := by
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_1873
      · exact prime_nonG_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166895539) ^ 83447769 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 55631846 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 89106 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 11238 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_33484585780649 : Nat.Prime 33484585780649 := by
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_31
      · exact prime_nonG_809
      · exact prime_nonG_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33484585780649) ^ 16742292890324 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 1080147928408 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 41390093672 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 200632 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_52107281 : Nat.Prime 52107281 := by
  apply lucas_primality 52107281 (3 : ZMod 52107281)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (31, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (31, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod = 52107281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_31
      · exact prime_nonG_21011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52107281) ^ 26053640 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52107281) ^ 10421456 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52107281) ^ 1680880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52107281) ^ 2480 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_39117456919511 : Nat.Prime 39117456919511 := by
  apply lucas_primality 39117456919511 (17 : ZMod 39117456919511)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (41, 1), (1831, 1), (52107281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (41, 1), (1831, 1), (52107281, 1)] : List FactorBlock).map factorBlockValue).prod = 39117456919511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_41
      · exact prime_nonG_1831
      · exact prime_nonG_52107281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 39117456919511) ^ 19558728459755 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 39117456919511) ^ 7823491383902 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 39117456919511) ^ 954084315110 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 39117456919511) ^ 21363985210 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 39117456919511) ^ 750710 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_93970853 : Nat.Prime 93970853 := by
  apply lucas_primality 93970853 (2 : ZMod 93970853)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (41, 1), (572993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (41, 1), (572993, 1)] : List FactorBlock).map factorBlockValue).prod = 93970853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_41
      · exact prime_nonG_572993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93970853) ^ 46985426 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93970853) ^ 2291972 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93970853) ^ 164 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_68572974676279 : Nat.Prime 68572974676279 := by
  apply lucas_primality 68572974676279 (3 : ZMod 68572974676279)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (121621, 1), (93970853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (121621, 1), (93970853, 1)] : List FactorBlock).map factorBlockValue).prod = 68572974676279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_121621
      · exact prime_nonG_93970853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 68572974676279) ^ 34286487338139 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68572974676279) ^ 22857658225426 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68572974676279) ^ 563825118 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68572974676279) ^ 729726 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_161735950924213 : Nat.Prime 161735950924213 := by
  apply lucas_primality 161735950924213 (2 : ZMod 161735950924213)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod = 161735950924213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_79
      · exact prime_nonG_877
      · exact prime_nonG_13751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161735950924213) ^ 80867975462106 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 53911983641404 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 23105135846316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3761301184284 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3441190445196 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 2047290518028 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 184419556356 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 11761759212 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_162965554863959 : Nat.Prime 162965554863959 := by
  apply lucas_primality 162965554863959 (7 : ZMod 162965554863959)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (53, 1), (1429, 1), (13972271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (53, 1), (1429, 1), (13972271, 1)] : List FactorBlock).map factorBlockValue).prod = 162965554863959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_53
      · exact prime_nonG_1429
      · exact prime_nonG_13972271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 162965554863959) ^ 81482777431979 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 162965554863959) ^ 23280793551994 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 162965554863959) ^ 14815050442178 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 162965554863959) ^ 3074821789886 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 162965554863959) ^ 114041675902 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 162965554863959) ^ 11663498 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_206255523187661 : Nat.Prime 206255523187661 := by
  apply lucas_primality 206255523187661 (2 : ZMod 206255523187661)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1327, 1), (12487, 1), (622367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1327, 1), (12487, 1), (622367, 1)] : List FactorBlock).map factorBlockValue).prod = 206255523187661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_1327
      · exact prime_nonG_12487
      · exact prime_nonG_622367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 206255523187661) ^ 103127761593830 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 206255523187661) ^ 41251104637532 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 206255523187661) ^ 155429934580 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 206255523187661) ^ 16517620180 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 206255523187661) ^ 331404980 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_23
      · exact prime_nonG_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_37
      · exact prime_nonG_443
      · exact prime_nonG_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_37
      · exact prime_nonG_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_86001505063 : Nat.Prime 86001505063 := by
  apply lucas_primality 86001505063 (3 : ZMod 86001505063)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (1367, 1), (953221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (1367, 1), (953221, 1)] : List FactorBlock).map factorBlockValue).prod = 86001505063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11
      · exact prime_nonG_1367
      · exact prime_nonG_953221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 86001505063) ^ 43000752531 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 86001505063) ^ 28667168354 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 86001505063) ^ 7818318642 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 86001505063) ^ 62912586 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 86001505063) ^ 90222 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1537706910526441 : Nat.Prime 1537706910526441 := by
  apply lucas_primality 1537706910526441 (11 : ZMod 1537706910526441)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (149, 1), (86001505063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (149, 1), (86001505063, 1)] : List FactorBlock).map factorBlockValue).prod = 1537706910526441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_149
      · exact prime_nonG_86001505063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1537706910526441) ^ 768853455263220 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1537706910526441) ^ 512568970175480 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1537706910526441) ^ 307541382105288 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1537706910526441) ^ 10320180607560 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1537706910526441) ^ 17880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_7332680171 : Nat.Prime 7332680171 := by
  apply lucas_primality 7332680171 (2 : ZMod 7332680171)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (31, 1), (419, 1), (56453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (31, 1), (419, 1), (56453, 1)] : List FactorBlock).map factorBlockValue).prod = 7332680171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_31
      · exact prime_nonG_419
      · exact prime_nonG_56453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7332680171) ^ 3666340085 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7332680171) ^ 1466536034 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7332680171) ^ 236538070 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7332680171) ^ 17500430 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7332680171) ^ 129890 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1772088816925571 : Nat.Prime 1772088816925571 := by
  apply lucas_primality 1772088816925571 (10 : ZMod 1772088816925571)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (13, 3), (7332680171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (13, 3), (7332680171, 1)] : List FactorBlock).map factorBlockValue).prod = 1772088816925571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_7332680171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1772088816925571) ^ 886044408462785 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1772088816925571) ^ 354417763385114 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1772088816925571) ^ 161098983356870 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1772088816925571) ^ 136314524378890 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1772088816925571) ^ 241670 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1793775758729587 : Nat.Prime 1793775758729587 := by
  apply lucas_primality 1793775758729587 (2 : ZMod 1793775758729587)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod = 1793775758729587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_26921
      · exact prime_nonG_96293
      · exact prime_nonG_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1793775758729587) ^ 896887879364793 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 597925252909862 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 66631096866 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 18628309002 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 15553823118 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_29623871 : Nat.Prime 29623871 := by
  apply lucas_primality 29623871 (7 : ZMod 29623871)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod = 29623871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_409
      · exact prime_nonG_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29623871) ^ 14811935 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 5924774 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 72430 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 4090 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_59247743 : Nat.Prime 59247743 := by
  apply lucas_primality 59247743 (5 : ZMod 59247743)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod = 59247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_29623871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59247743) ^ 29623871 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 59247743) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2743295750628703 : Nat.Prime 2743295750628703 := by
  apply lucas_primality 2743295750628703 (5 : ZMod 2743295750628703)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod = 2743295750628703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_2531
      · exact prime_nonG_3049
      · exact prime_nonG_59247743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2743295750628703) ^ 1371647875314351 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 914431916876234 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 1083878210442 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 899736225198 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 46302114 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2500457660201 : Nat.Prime 2500457660201 := by
  apply lucas_primality 2500457660201 (3 : ZMod 2500457660201)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (41, 1), (3511, 1), (86851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (41, 1), (3511, 1), (86851, 1)] : List FactorBlock).map factorBlockValue).prod = 2500457660201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_41
      · exact prime_nonG_3511
      · exact prime_nonG_86851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2500457660201) ^ 1250228830100 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 500091532040 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 60986772200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 712178200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 28790200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_5145941864693659 : Nat.Prime 5145941864693659 := by
  apply lucas_primality 5145941864693659 (3 : ZMod 5145941864693659)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 3), (2500457660201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 3), (2500457660201, 1)] : List FactorBlock).map factorBlockValue).prod = 5145941864693659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_2500457660201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5145941864693659) ^ 2572970932346829 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 1715313954897886 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 735134552099094 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 2058 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_5577088447446539 : Nat.Prime 5577088447446539 := by
  apply lucas_primality 5577088447446539 (2 : ZMod 5577088447446539)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (43, 1), (881, 1), (1061, 1), (6307033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (43, 1), (881, 1), (1061, 1), (6307033, 1)] : List FactorBlock).map factorBlockValue).prod = 5577088447446539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_43
      · exact prime_nonG_881
      · exact prime_nonG_1061
      · exact prime_nonG_6307033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5577088447446539) ^ 2788544223723269 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 507008040676958 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 129699731335966 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 6330406864298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 5256445285058 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 884264986 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_20025517 : Nat.Prime 20025517 := by
  apply lucas_primality 20025517 (2 : ZMod 20025517)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod = 20025517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_34057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20025517) ^ 10012758 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 6675172 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 2860788 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 588 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_19
      · exact prime_nonG_61
      · exact prime_nonG_67
      · exact prime_nonG_463
      · exact prime_nonG_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_8213087550976673 : Nat.Prime 8213087550976673 := by
  apply lucas_primality 8213087550976673 (3 : ZMod 8213087550976673)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (13, 1), (569, 1), (2399, 1), (2066201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (13, 1), (569, 1), (2399, 1), (2066201, 1)] : List FactorBlock).map factorBlockValue).prod = 8213087550976673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_13
      · exact prime_nonG_569
      · exact prime_nonG_2399
      · exact prime_nonG_2066201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8213087550976673) ^ 4106543775488336 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 1173298221568096 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 631775965459744 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 14434248771488 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 3423546290528 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 3974970272 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_101769837067 : Nat.Prime 101769837067 := by
  apply lucas_primality 101769837067 (5 : ZMod 101769837067)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 2), (97, 1), (161461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 2), (97, 1), (161461, 1)] : List FactorBlock).map factorBlockValue).prod = 101769837067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_97
      · exact prime_nonG_161461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 101769837067) ^ 50884918533 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 101769837067) ^ 33923279022 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 101769837067) ^ 5356307214 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 101769837067) ^ 1049173578 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 101769837067) ^ 630306 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_9099851751182873 : Nat.Prime 9099851751182873 := by
  apply lucas_primality 9099851751182873 (3 : ZMod 9099851751182873)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11177, 1), (101769837067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11177, 1), (101769837067, 1)] : List FactorBlock).map factorBlockValue).prod = 9099851751182873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11177
      · exact prime_nonG_101769837067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9099851751182873) ^ 4549925875591436 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9099851751182873) ^ 814158696536 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9099851751182873) ^ 89416 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_173
      · exact prime_nonG_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_4159
      · exact prime_nonG_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_27238268144131903 : Nat.Prime 27238268144131903 := by
  apply lucas_primality 27238268144131903 (3 : ZMod 27238268144131903)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod = 27238268144131903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_103
      · exact prime_nonG_82529
      · exact prime_nonG_1244879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27238268144131903) ^ 13619134072065951 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 9079422714710634 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2476206194921082 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2095251395702454 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 264449205282834 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 330044810238 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 21880253538 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2296112521061 : Nat.Prime 2296112521061 := by
  apply lucas_primality 2296112521061 (2 : ZMod 2296112521061)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (311, 1), (599, 1), (616277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (311, 1), (599, 1), (616277, 1)] : List FactorBlock).map factorBlockValue).prod = 2296112521061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_311
      · exact prime_nonG_599
      · exact prime_nonG_616277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2296112521061) ^ 1148056260530 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 459222504212 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 7382998460 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 3833242940 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 3725780 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4592225042123 : Nat.Prime 4592225042123 := by
  apply lucas_primality 4592225042123 (2 : ZMod 4592225042123)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2296112521061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2296112521061, 1)] : List FactorBlock).map factorBlockValue).prod = 4592225042123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_2296112521061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4592225042123) ^ 2296112521061 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4592225042123) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_34854988069713571 : Nat.Prime 34854988069713571 := by
  apply lucas_primality 34854988069713571 (2 : ZMod 34854988069713571)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4592225042123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4592225042123, 1)] : List FactorBlock).map factorBlockValue).prod = 34854988069713571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_23
      · exact prime_nonG_4592225042123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34854988069713571) ^ 17427494034856785 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 11618329356571190 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 6970997613942714 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 3168635279064870 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 1515434263900590 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 7590 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1522625983 : Nat.Prime 1522625983 := by
  apply lucas_primality 1522625983 (7 : ZMod 1522625983)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (359, 1), (706883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (359, 1), (706883, 1)] : List FactorBlock).map factorBlockValue).prod = 1522625983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_359
      · exact prime_nonG_706883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1522625983) ^ 761312991 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1522625983) ^ 507541994 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1522625983) ^ 4241298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1522625983) ^ 2154 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_76648093634890031 : Nat.Prime 76648093634890031 := by
  apply lucas_primality 76648093634890031 (7 : ZMod 76648093634890031)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (23, 1), (101, 1), (197, 1), (1522625983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (23, 1), (101, 1), (197, 1), (1522625983, 1)] : List FactorBlock).map factorBlockValue).prod = 76648093634890031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_23
      · exact prime_nonG_101
      · exact prime_nonG_197
      · exact prime_nonG_1522625983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76648093634890031) ^ 38324046817445015 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 15329618726978006 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 6968008512262730 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 3332525810212610 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 758892016187030 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 389076617435990 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76648093634890031) ^ 50339410 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_149
      · exact prime_nonG_929
      · exact prime_nonG_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_17
      · exact prime_nonG_47
      · exact prime_nonG_81047
      · exact prime_nonG_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1453717894039 : Nat.Prime 1453717894039 := by
  apply lucas_primality 1453717894039 (3 : ZMod 1453717894039)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (521, 1), (2411, 1), (192883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (521, 1), (2411, 1), (192883, 1)] : List FactorBlock).map factorBlockValue).prod = 1453717894039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_521
      · exact prime_nonG_2411
      · exact prime_nonG_192883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1453717894039) ^ 726858947019 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453717894039) ^ 484572631346 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453717894039) ^ 2790245478 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453717894039) ^ 602952258 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1453717894039) ^ 7536786 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_144822284039953259 : Nat.Prime 144822284039953259 := by
  apply lucas_primality 144822284039953259 (2 : ZMod 144822284039953259)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (49811, 1), (1453717894039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (49811, 1), (1453717894039, 1)] : List FactorBlock).map factorBlockValue).prod = 144822284039953259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_49811
      · exact prime_nonG_1453717894039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144822284039953259) ^ 72411142019976629 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 144822284039953259) ^ 2907435788078 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 144822284039953259) ^ 99622 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_318927438253 : Nat.Prime 318927438253 := by
  apply lucas_primality 318927438253 (5 : ZMod 318927438253)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod = 318927438253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_761
      · exact prime_nonG_11641387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 318927438253) ^ 159463719126 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 106309146084 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 419089932 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 27396 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_157435978474087427 : Nat.Prime 157435978474087427 := by
  apply lucas_primality 157435978474087427 (2 : ZMod 157435978474087427)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod = 157435978474087427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_53
      · exact prime_nonG_4657
      · exact prime_nonG_318927438253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157435978474087427) ^ 78717989237043713 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 2970490159888442 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 33806308454818 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 493642 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3074820748067 : Nat.Prime 3074820748067 := by
  apply lucas_primality 3074820748067 (2 : ZMod 3074820748067)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod = 3074820748067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_103
      · exact prime_nonG_86843
      · exact prime_nonG_171877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3074820748067) ^ 1537410374033 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 29852628622 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 35406662 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 17889658 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_43047490472939 : Nat.Prime 43047490472939 := by
  apply lucas_primality 43047490472939 (7 : ZMod 43047490472939)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod = 43047490472939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_3074820748067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43047490472939) ^ 21523745236469 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 6149641496134 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 14 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_377440396466729153 : Nat.Prime 377440396466729153 := by
  apply lucas_primality 377440396466729153 (3 : ZMod 377440396466729153)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod = 377440396466729153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_137
      · exact prime_nonG_43047490472939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377440396466729153) ^ 188720198233364576 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 2755039390268096 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 8768 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_5037757
      · exact prime_nonG_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_17
      · exact prime_nonG_397
      · exact prime_nonG_2531
      · exact prime_nonG_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_41
      · exact prime_nonG_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_29
      · exact prime_nonG_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_579848016567285199 : Nat.Prime 579848016567285199 := by
  apply lucas_primality 579848016567285199 (3 : ZMod 579848016567285199)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod = 579848016567285199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_10531
      · exact prime_nonG_418069
      · exact prime_nonG_7316849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 579848016567285199) ^ 289924008283642599 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 193282672189095066 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 55061059402458 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 1386967262742 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 79248323502 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_117010237 : Nat.Prime 117010237 := by
  apply lucas_primality 117010237 (6 : ZMod 117010237)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (198997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (198997, 1)] : List FactorBlock).map factorBlockValue).prod = 117010237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_198997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 117010237) ^ 58505118 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 117010237) ^ 39003412 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 117010237) ^ 16715748 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 117010237) ^ 588 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2045009436082096151 : Nat.Prime 2045009436082096151 := by
  apply lucas_primality 2045009436082096151 (13 : ZMod 2045009436082096151)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (557, 1), (627547, 1), (117010237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (557, 1), (627547, 1), (117010237, 1)] : List FactorBlock).map factorBlockValue).prod = 2045009436082096151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_557
      · exact prime_nonG_627547
      · exact prime_nonG_117010237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2045009436082096151) ^ 1022504718041048075 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2045009436082096151) ^ 409001887216419230 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2045009436082096151) ^ 3671471159931950 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2045009436082096151) ^ 3258735100450 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2045009436082096151) ^ 17477183950 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_223218599 : Nat.Prime 223218599 := by
  apply lucas_primality 223218599 (7 : ZMod 223218599)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2791, 1), (39989, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2791, 1), (39989, 1)] : List FactorBlock).map factorBlockValue).prod = 223218599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_2791
      · exact prime_nonG_39989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 223218599) ^ 111609299 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 223218599) ^ 79978 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 223218599) ^ 5582 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3486096414137817049 : Nat.Prime 3486096414137817049 := by
  apply lucas_primality 3486096414137817049 (13 : ZMod 3486096414137817049)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (199, 1), (3269977, 1), (223218599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (199, 1), (3269977, 1), (223218599, 1)] : List FactorBlock).map factorBlockValue).prod = 3486096414137817049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_199
      · exact prime_nonG_3269977
      · exact prime_nonG_223218599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3486096414137817049) ^ 1743048207068908524 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 3486096414137817049) ^ 1162032138045939016 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 3486096414137817049) ^ 17518072432853352 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 3486096414137817049) ^ 1066092028824 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 3486096414137817049) ^ 15617410152 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_7438713253 : Nat.Prime 7438713253 := by
  apply lucas_primality 7438713253 (2 : ZMod 7438713253)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 1), (19996541, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 1), (19996541, 1)] : List FactorBlock).map factorBlockValue).prod = 7438713253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_31
      · exact prime_nonG_19996541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7438713253) ^ 3719356626 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 2479571084 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 239958492 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 372 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_10390866777165714899 : Nat.Prime 10390866777165714899 := by
  apply lucas_primality 10390866777165714899 (2 : ZMod 10390866777165714899)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (211, 1), (1103, 1), (3001, 1), (7438713253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (211, 1), (1103, 1), (3001, 1), (7438713253, 1)] : List FactorBlock).map factorBlockValue).prod = 10390866777165714899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_211
      · exact prime_nonG_1103
      · exact prime_nonG_3001
      · exact prime_nonG_7438713253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10390866777165714899) ^ 5195433388582857449 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 49245814109790118 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 9420550115290766 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 3462468103020898 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 1396863466 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_13
      · exact prime_nonG_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_19
      · exact prime_nonG_1823
      · exact prime_nonG_3271
      · exact prime_nonG_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_67
      · exact prime_nonG_28807
      · exact prime_nonG_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_23
      · exact prime_nonG_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_101598183671 : Nat.Prime 101598183671 := by
  apply lucas_primality 101598183671 (17 : ZMod 101598183671)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod = 101598183671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_8521
      · exact prime_nonG_1192327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 101598183671) ^ 50799091835 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 20319636734 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 11923270 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 85210 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_203196367343 : Nat.Prime 203196367343 := by
  apply lucas_primality 203196367343 (5 : ZMod 203196367343)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod = 203196367343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_101598183671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203196367343) ^ 101598183671 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 203196367343) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1211050349364281 : Nat.Prime 1211050349364281 := by
  apply lucas_primality 1211050349364281 (3 : ZMod 1211050349364281)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod = 1211050349364281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_149
      · exact prime_nonG_203196367343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1211050349364281) ^ 605525174682140 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 242210069872856 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 8127854693720 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 5960 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_16090014941653837367 : Nat.Prime 16090014941653837367 := by
  apply lucas_primality 16090014941653837367 (5 : ZMod 16090014941653837367)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod = 16090014941653837367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_13
      · exact prime_nonG_73
      · exact prime_nonG_1211050349364281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16090014941653837367) ^ 8045007470826918683 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 2298573563093405338 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 1237693457050295182 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 220411163584299142 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 13286 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_6593632097779193 : Nat.Prime 6593632097779193 := by
  apply lucas_primality 6593632097779193 (5 : ZMod 6593632097779193)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (269, 1), (34147, 1), (4722547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (269, 1), (34147, 1), (4722547, 1)] : List FactorBlock).map factorBlockValue).prod = 6593632097779193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_19
      · exact prime_nonG_269
      · exact prime_nonG_34147
      · exact prime_nonG_4722547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6593632097779193) ^ 3296816048889596 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593632097779193) ^ 347033268304168 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593632097779193) ^ 24511643486168 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593632097779193) ^ 193095501736 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6593632097779193) ^ 1396202536 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_39799163342195208949 : Nat.Prime 39799163342195208949 := by
  apply lucas_primality 39799163342195208949 (10 : ZMod 39799163342195208949)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (503, 1), (6593632097779193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (503, 1), (6593632097779193, 1)] : List FactorBlock).map factorBlockValue).prod = 39799163342195208949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_503
      · exact prime_nonG_6593632097779193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 39799163342195208949) ^ 19899581671097604474 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 39799163342195208949) ^ 13266387780731736316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 39799163342195208949) ^ 79123585173350316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 39799163342195208949) ^ 6036 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5437
      · exact prime_nonG_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_223
      · exact prime_nonG_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_821
      · exact prime_nonG_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_347
      · exact prime_nonG_109481
      · exact prime_nonG_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_33749
      · exact prime_nonG_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1097751731 : Nat.Prime 1097751731 := by
  apply lucas_primality 1097751731 (2 : ZMod 1097751731)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (43, 1), (61, 1), (41851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (43, 1), (61, 1), (41851, 1)] : List FactorBlock).map factorBlockValue).prod = 1097751731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_43
      · exact prime_nonG_61
      · exact prime_nonG_41851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1097751731) ^ 548875865 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097751731) ^ 219550346 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097751731) ^ 25529110 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097751731) ^ 17995930 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097751731) ^ 26230 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2195503463 : Nat.Prime 2195503463 := by
  apply lucas_primality 2195503463 (5 : ZMod 2195503463)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1097751731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1097751731, 1)] : List FactorBlock).map factorBlockValue).prod = 2195503463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1097751731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2195503463) ^ 1097751731 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195503463) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_250287394783 : Nat.Prime 250287394783 := by
  apply lucas_primality 250287394783 (17 : ZMod 250287394783)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (2195503463, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (2195503463, 1)] : List FactorBlock).map factorBlockValue).prod = 250287394783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_2195503463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 250287394783) ^ 125143697391 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 250287394783) ^ 83429131594 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 250287394783) ^ 13173020778 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 250287394783) ^ 114 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4004598316529 : Nat.Prime 4004598316529 := by
  apply lucas_primality 4004598316529 (3 : ZMod 4004598316529)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (250287394783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (250287394783, 1)] : List FactorBlock).map factorBlockValue).prod = 4004598316529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_250287394783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4004598316529) ^ 2002299158264 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4004598316529) ^ 16 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_116049847295244737293 : Nat.Prime 116049847295244737293 := by
  apply lucas_primality 116049847295244737293 (2 : ZMod 116049847295244737293)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (59, 1), (61, 2), (4004598316529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (59, 1), (61, 2), (4004598316529, 1)] : List FactorBlock).map factorBlockValue).prod = 116049847295244737293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11
      · exact prime_nonG_59
      · exact prime_nonG_61
      · exact prime_nonG_4004598316529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116049847295244737293) ^ 58024923647622368646 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116049847295244737293) ^ 38683282431748245764 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116049847295244737293) ^ 10549986117749521572 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116049847295244737293) ^ 1966946564326181988 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116049847295244737293) ^ 1902456513036798972 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116049847295244737293) ^ 28979148 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_14615833261 : Nat.Prime 14615833261 := by
  apply lucas_primality 14615833261 (6 : ZMod 14615833261)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod = 14615833261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_181
      · exact prime_nonG_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14615833261) ^ 7307916630 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 4871944420 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 2923166652 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 2087976180 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 80750460 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 76020 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_175389999133 : Nat.Prime 175389999133 := by
  apply lucas_primality 175389999133 (2 : ZMod 175389999133)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod = 175389999133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_14615833261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 175389999133) ^ 87694999566 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 175389999133) ^ 58463333044 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 175389999133) ^ 12 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1052339994799 : Nat.Prime 1052339994799 := by
  apply lucas_primality 1052339994799 (6 : ZMod 1052339994799)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod = 1052339994799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_175389999133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1052339994799) ^ 526169997399 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052339994799) ^ 350779998266 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052339994799) ^ 6 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_138104211745804923847 : Nat.Prime 138104211745804923847 := by
  apply lucas_primality 138104211745804923847 (5 : ZMod 138104211745804923847)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod = 138104211745804923847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7290853
      · exact prime_nonG_1052339994799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 138104211745804923847) ^ 69052105872902461923 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 46034737248601641282 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 18942119906382 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 131235354 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_313029089 : Nat.Prime 313029089 := by
  apply lucas_primality 313029089 (3 : ZMod 313029089)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (97, 1), (100847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (97, 1), (100847, 1)] : List FactorBlock).map factorBlockValue).prod = 313029089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_97
      · exact prime_nonG_100847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 313029089) ^ 156514544 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 313029089) ^ 3227104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 313029089) ^ 3104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_182285639490921488611 : Nat.Prime 182285639490921488611 := by
  apply lucas_primality 182285639490921488611 (2 : ZMod 182285639490921488611)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (131, 1), (13470463, 1), (313029089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (131, 1), (13470463, 1), (313029089, 1)] : List FactorBlock).map factorBlockValue).prod = 182285639490921488611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_131
      · exact prime_nonG_13470463
      · exact prime_nonG_313029089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 182285639490921488611) ^ 91142819745460744305 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 60761879830307162870 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 36457127898184297722 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 16571421771901953510 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 1391493431228408310 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 13532247517470 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 182285639490921488611) ^ 582328115490 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_55235879 : Nat.Prime 55235879 := by
  apply lucas_primality 55235879 (17 : ZMod 55235879)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1123, 1), (24593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1123, 1), (24593, 1)] : List FactorBlock).map factorBlockValue).prod = 55235879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1123
      · exact prime_nonG_24593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 55235879) ^ 27617939 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 55235879) ^ 49186 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (17 : ZMod 55235879) ^ 2246 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_143834228917 : Nat.Prime 143834228917 := by
  apply lucas_primality 143834228917 (13 : ZMod 143834228917)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (31, 1), (55235879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (31, 1), (55235879, 1)] : List FactorBlock).map factorBlockValue).prod = 143834228917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_31
      · exact prime_nonG_55235879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 143834228917) ^ 71917114458 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 47944742972 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 20547746988 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 4639813836 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 2604 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_289835118837045663367 : Nat.Prime 289835118837045663367 := by
  apply lucas_primality 289835118837045663367 (3 : ZMod 289835118837045663367)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (109, 1), (3081137, 1), (143834228917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (109, 1), (3081137, 1), (143834228917, 1)] : List FactorBlock).map factorBlockValue).prod = 289835118837045663367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_109
      · exact prime_nonG_3081137
      · exact prime_nonG_143834228917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 289835118837045663367) ^ 144917559418522831683 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 96611706279015221122 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 2659037787495831774 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 94067585711718 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 2015063598 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3811082473401769759 : Nat.Prime 3811082473401769759 := by
  apply lucas_primality 3811082473401769759 (3 : ZMod 3811082473401769759)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (109, 1), (113, 1), (239, 1), (13397, 1), (16105963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (109, 1), (113, 1), (239, 1), (13397, 1), (16105963, 1)] : List FactorBlock).map factorBlockValue).prod = 3811082473401769759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_109
      · exact prime_nonG_113
      · exact prime_nonG_239
      · exact prime_nonG_13397
      · exact prime_nonG_16105963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3811082473401769759) ^ 1905541236700884879 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 1270360824467256586 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 34964059389007062 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 33726393569927166 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 15945951771555522 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 284472827752614 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3811082473401769759) ^ 236625557466 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_358241752499766357347 : Nat.Prime 358241752499766357347 := by
  apply lucas_primality 358241752499766357347 (5 : ZMod 358241752499766357347)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (3811082473401769759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (3811082473401769759, 1)] : List FactorBlock).map factorBlockValue).prod = 358241752499766357347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_47
      · exact prime_nonG_3811082473401769759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 358241752499766357347) ^ 179120876249883178673 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 358241752499766357347) ^ 7622164946803539518 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 358241752499766357347) ^ 94 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_40430077 : Nat.Prime 40430077 := by
  apply lucas_primality 40430077 (5 : ZMod 40430077)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 1), (251, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 1), (251, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod = 40430077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_31
      · exact prime_nonG_251
      · exact prime_nonG_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40430077) ^ 20215038 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430077) ^ 13476692 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430077) ^ 1304196 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430077) ^ 161076 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430077) ^ 93372 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_63716381 : Nat.Prime 63716381 := by
  apply lucas_primality 63716381 (2 : ZMod 63716381)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (13, 2), (2693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (13, 2), (2693, 1)] : List FactorBlock).map factorBlockValue).prod = 63716381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_13
      · exact prime_nonG_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63716381) ^ 31858190 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63716381) ^ 12743276 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63716381) ^ 9102340 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63716381) ^ 4901260 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 63716381) ^ 23660 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_127432763 : Nat.Prime 127432763 := by
  apply lucas_primality 127432763 (2 : ZMod 127432763)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (63716381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (63716381, 1)] : List FactorBlock).map factorBlockValue).prod = 127432763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_63716381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 127432763) ^ 63716381 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 127432763) ^ 2 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1017027781389477047401 : Nat.Prime 1017027781389477047401 := by
  apply lucas_primality 1017027781389477047401 (29 : ZMod 1017027781389477047401)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (7, 1), (47, 1), (40430077, 1), (127432763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (7, 1), (47, 1), (40430077, 1), (127432763, 1)] : List FactorBlock).map factorBlockValue).prod = 1017027781389477047401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_47
      · exact prime_nonG_40430077
      · exact prime_nonG_127432763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1017027781389477047401) ^ 508513890694738523700 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 339009260463159015800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 203405556277895409480 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 145289683055639578200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 21638888965733554200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 25155227416200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (29 : ZMod 1017027781389477047401) ^ 7980897199800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4153387267 : Nat.Prime 4153387267 := by
  apply lucas_primality 4153387267 (5 : ZMod 4153387267)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (7, 1), (17, 1), (215447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (7, 1), (17, 1), (215447, 1)] : List FactorBlock).map factorBlockValue).prod = 4153387267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_17
      · exact prime_nonG_215447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4153387267) ^ 2076693633 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4153387267) ^ 1384462422 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4153387267) ^ 593341038 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4153387267) ^ 244316898 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4153387267) ^ 19278 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_15272295717867691 : Nat.Prime 15272295717867691 := by
  apply lucas_primality 15272295717867691 (2 : ZMod 15272295717867691)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (19, 1), (6451, 1), (4153387267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (19, 1), (6451, 1), (4153387267, 1)] : List FactorBlock).map factorBlockValue).prod = 15272295717867691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_19
      · exact prime_nonG_6451
      · exact prime_nonG_4153387267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15272295717867691) ^ 7636147858933845 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15272295717867691) ^ 5090765239289230 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15272295717867691) ^ 3054459143573538 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15272295717867691) ^ 803805037782510 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15272295717867691) ^ 2367430742190 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15272295717867691) ^ 3677070 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1366687199200543932209 : Nat.Prime 1366687199200543932209 := by
  apply lucas_primality 1366687199200543932209 (6 : ZMod 1366687199200543932209)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (17, 1), (47, 1), (15272295717867691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (17, 1), (47, 1), (15272295717867691, 1)] : List FactorBlock).map factorBlockValue).prod = 1366687199200543932209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_17
      · exact prime_nonG_47
      · exact prime_nonG_15272295717867691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1366687199200543932209) ^ 683343599600271966104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1366687199200543932209) ^ 195241028457220561744 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1366687199200543932209) ^ 80393364658855525424 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1366687199200543932209) ^ 29078451046820083664 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1366687199200543932209) ^ 89488 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_79
      · exact prime_nonG_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_31
      · exact prime_nonG_2161
      · exact prime_nonG_8537
      · exact prime_nonG_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_35279
      · exact prime_nonG_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_61717
      · exact prime_nonG_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_19
      · exact prime_nonG_107
      · exact prime_nonG_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_760936573 : Nat.Prime 760936573 := by
  apply lucas_primality 760936573 (5 : ZMod 760936573)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (11, 2), (58229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (11, 2), (58229, 1)] : List FactorBlock).map factorBlockValue).prod = 760936573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11
      · exact prime_nonG_58229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 760936573) ^ 380468286 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 760936573) ^ 253645524 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 760936573) ^ 69176052 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 760936573) ^ 13068 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3507042480718718925647 : Nat.Prime 3507042480718718925647 := by
  apply lucas_primality 3507042480718718925647 (5 : ZMod 3507042480718718925647)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (379, 1), (16631, 1), (28123, 1), (760936573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (379, 1), (16631, 1), (28123, 1), (760936573, 1)] : List FactorBlock).map factorBlockValue).prod = 3507042480718718925647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_13
      · exact prime_nonG_379
      · exact prime_nonG_16631
      · exact prime_nonG_28123
      · exact prime_nonG_760936573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3507042480718718925647) ^ 1753521240359359462823 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3507042480718718925647) ^ 269772498516824532742 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3507042480718718925647) ^ 9253410239363374474 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3507042480718718925647) ^ 210873818815388066 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3507042480718718925647) ^ 124703711578377802 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3507042480718718925647) ^ 4608849942502 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_20250227 : Nat.Prime 20250227 := by
  apply lucas_primality 20250227 (2 : ZMod 20250227)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (347, 1), (29179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (347, 1), (29179, 1)] : List FactorBlock).map factorBlockValue).prod = 20250227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_347
      · exact prime_nonG_29179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20250227) ^ 10125113 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20250227) ^ 58358 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20250227) ^ 694 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3037534051 : Nat.Prime 3037534051 := by
  apply lucas_primality 3037534051 (2 : ZMod 3037534051)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (20250227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (20250227, 1)] : List FactorBlock).map factorBlockValue).prod = 3037534051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_20250227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3037534051) ^ 1518767025 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3037534051) ^ 1012511350 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3037534051) ^ 607506810 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3037534051) ^ 150 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2235825538783367 : Nat.Prime 2235825538783367 := by
  apply lucas_primality 2235825538783367 (5 : ZMod 2235825538783367)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (21649, 1), (3037534051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (21649, 1), (3037534051, 1)] : List FactorBlock).map factorBlockValue).prod = 2235825538783367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_17
      · exact prime_nonG_21649
      · exact prime_nonG_3037534051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2235825538783367) ^ 1117912769391683 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2235825538783367) ^ 131519149340198 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2235825538783367) ^ 103276157734 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2235825538783367) ^ 736066 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_8428655360965235017207 : Nat.Prime 8428655360965235017207 := by
  apply lucas_primality 8428655360965235017207 (5 : ZMod 8428655360965235017207)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (17, 1), (2843, 1), (2235825538783367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (17, 1), (2843, 1), (2235825538783367, 1)] : List FactorBlock).map factorBlockValue).prod = 8428655360965235017207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_2843
      · exact prime_nonG_2235825538783367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8428655360965235017207) ^ 4214327680482617508603 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8428655360965235017207) ^ 2809551786988411672402 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8428655360965235017207) ^ 648358104689633462862 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8428655360965235017207) ^ 495803256527366765718 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8428655360965235017207) ^ 2964704664426744642 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8428655360965235017207) ^ 3769818 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_668729401 : Nat.Prime 668729401 := by
  apply lucas_primality 668729401 (11 : ZMod 668729401)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (1114549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (1114549, 1)] : List FactorBlock).map factorBlockValue).prod = 668729401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_1114549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 668729401) ^ 334364700 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 222909800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 133745880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3163360712218255117 : Nat.Prime 3163360712218255117 := by
  apply lucas_primality 3163360712218255117 (2 : ZMod 3163360712218255117)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (29, 1), (43, 1), (105373, 1), (668729401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (29, 1), (43, 1), (105373, 1), (668729401, 1)] : List FactorBlock).map factorBlockValue).prod = 3163360712218255117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_29
      · exact prime_nonG_43
      · exact prime_nonG_105373
      · exact prime_nonG_668729401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3163360712218255117) ^ 1581680356109127558 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 1054453570739418372 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 109081403869595004 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 73566528191122212 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 30020600269692 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 4730404716 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_11476672663927829564477 : Nat.Prime 11476672663927829564477 := by
  apply lucas_primality 11476672663927829564477 (2 : ZMod 11476672663927829564477)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (907, 1), (3163360712218255117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (907, 1), (3163360712218255117, 1)] : List FactorBlock).map factorBlockValue).prod = 11476672663927829564477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_907
      · exact prime_nonG_3163360712218255117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11476672663927829564477) ^ 5738336331963914782238 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476672663927829564477) ^ 12653442848873020468 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476672663927829564477) ^ 3628 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_98880083 : Nat.Prime 98880083 := by
  apply lucas_primality 98880083 (6 : ZMod 98880083)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod = 98880083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_7
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_10589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98880083) ^ 49440041 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 14125726 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 4299134 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 3409658 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 9338 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1018963687663171715671 : Nat.Prime 1018963687663171715671 := by
  apply lucas_primality 1018963687663171715671 (3 : ZMod 1018963687663171715671)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod = 1018963687663171715671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_2939
      · exact prime_nonG_12986333
      · exact prime_nonG_98880083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1018963687663171715671) ^ 509481843831585857835 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 339654562554390571890 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 203792737532634343134 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 346704214924522530 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 78464312262990 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 10305044825490 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_18341346377937090882079 : Nat.Prime 18341346377937090882079 := by
  apply lucas_primality 18341346377937090882079 (3 : ZMod 18341346377937090882079)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod = 18341346377937090882079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_1018963687663171715671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18341346377937090882079) ^ 9170673188968545441039 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 6113782125979030294026 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 18 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_127
      · exact prime_nonG_193
      · exact prime_nonG_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_53
      · exact prime_nonG_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_167
      · exact prime_nonG_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_21580023643
      · exact prime_nonG_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4696532563 : Nat.Prime 4696532563 := by
  apply lucas_primality 4696532563 (2 : ZMod 4696532563)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod = 4696532563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_3823
      · exact prime_nonG_204749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4696532563) ^ 2348266281 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 1565510854 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 1228494 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 22938 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_7776862710917 : Nat.Prime 7776862710917 := by
  apply lucas_primality 7776862710917 (2 : ZMod 7776862710917)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod = 7776862710917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_13
      · exact prime_nonG_23
      · exact prime_nonG_1933
      · exact prime_nonG_3363887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7776862710917) ^ 3888431355458 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 598220208532 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 338124465692 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 4023208852 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 2311868 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_73048577919604292180543 : Nat.Prime 73048577919604292180543 := by
  apply lucas_primality 73048577919604292180543 (5 : ZMod 73048577919604292180543)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod = 73048577919604292180543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_4696532563
      · exact prime_nonG_7776862710917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73048577919604292180543) ^ 36524288959802146090271 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 73048577919604292180543) ^ 15553725421834 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 73048577919604292180543) ^ 9393065126 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_25214051 : Nat.Prime 25214051 := by
  apply lucas_primality 25214051 (6 : ZMod 25214051)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod = 25214051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_29
      · exact prime_nonG_17389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25214051) ^ 12607025 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 5042810 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 869450 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 1450 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2773545611 : Nat.Prime 2773545611 := by
  apply lucas_primality 2773545611 (2 : ZMod 2773545611)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod = 2773545611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_11
      · exact prime_nonG_25214051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2773545611) ^ 1386772805 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 554709122 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 252140510 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 110 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_11970622857077 : Nat.Prime 11970622857077 := by
  apply lucas_primality 11970622857077 (2 : ZMod 11970622857077)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod = 11970622857077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_13
      · exact prime_nonG_83
      · exact prime_nonG_2773545611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11970622857077) ^ 5985311428538 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 920817142852 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 144224371772 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 4316 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_55113911370054181597633 : Nat.Prime 55113911370054181597633 := by
  apply lucas_primality 55113911370054181597633 (5 : ZMod 55113911370054181597633)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod = 55113911370054181597633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_17
      · exact prime_nonG_109
      · exact prime_nonG_12941
      · exact prime_nonG_11970622857077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55113911370054181597633) ^ 27556955685027090798816 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 18371303790018060532544 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 3241994786473775388096 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 505632214404166803648 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4258860317599426752 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4604097216 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_330683468220325089585799 : Nat.Prime 330683468220325089585799 := by
  apply lucas_primality 330683468220325089585799 (6 : ZMod 330683468220325089585799)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod = 330683468220325089585799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_55113911370054181597633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 330683468220325089585799) ^ 165341734110162544792899 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 110227822740108363195266 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 6 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_30625937 : Nat.Prime 30625937 := by
  apply lucas_primality 30625937 (3 : ZMod 30625937)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (11, 1), (37, 1), (4703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (11, 1), (37, 1), (4703, 1)] : List FactorBlock).map factorBlockValue).prod = 30625937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_11
      · exact prime_nonG_37
      · exact prime_nonG_4703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30625937) ^ 15312968 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30625937) ^ 2784176 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30625937) ^ 827728 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30625937) ^ 6512 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_183755623 : Nat.Prime 183755623 := by
  apply lucas_primality 183755623 (3 : ZMod 183755623)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (30625937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (30625937, 1)] : List FactorBlock).map factorBlockValue).prod = 183755623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_30625937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 183755623) ^ 91877811 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 183755623) ^ 61251874 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 183755623) ^ 6 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1102533739 : Nat.Prime 1102533739 := by
  apply lucas_primality 1102533739 (2 : ZMod 1102533739)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (183755623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (183755623, 1)] : List FactorBlock).map factorBlockValue).prod = 1102533739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_183755623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1102533739) ^ 551266869 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102533739) ^ 367511246 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102533739) ^ 6 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_4410134957 : Nat.Prime 4410134957 := by
  apply lucas_primality 4410134957 (2 : ZMod 4410134957)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1102533739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1102533739, 1)] : List FactorBlock).map factorBlockValue).prod = 4410134957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_1102533739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4410134957) ^ 2205067478 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4410134957) ^ 4 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_417729348183315028564787 : Nat.Prime 417729348183315028564787 := by
  apply lucas_primality 417729348183315028564787 (2 : ZMod 417729348183315028564787)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (631, 1), (751, 1), (3557, 1), (28097, 1), (4410134957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (631, 1), (751, 1), (3557, 1), (28097, 1), (4410134957, 1)] : List FactorBlock).map factorBlockValue).prod = 417729348183315028564787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_631
      · exact prime_nonG_751
      · exact prime_nonG_3557
      · exact prime_nonG_28097
      · exact prime_nonG_4410134957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 417729348183315028564787) ^ 208864674091657514282393 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 417729348183315028564787) ^ 662011645298439031006 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 417729348183315028564787) ^ 556230823146890850286 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 417729348183315028564787) ^ 117438669716984826698 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 417729348183315028564787) ^ 14867400369552444338 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 417729348183315028564787) ^ 94720309527098 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_2316330535903 : Nat.Prime 2316330535903 := by
  apply lucas_primality 2316330535903 (5 : ZMod 2316330535903)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (53, 1), (101, 1), (4242317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (53, 1), (101, 1), (4242317, 1)] : List FactorBlock).map factorBlockValue).prod = 2316330535903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_17
      · exact prime_nonG_53
      · exact prime_nonG_101
      · exact prime_nonG_4242317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2316330535903) ^ 1158165267951 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316330535903) ^ 772110178634 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316330535903) ^ 136254737406 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316330535903) ^ 43704349734 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316330535903) ^ 22933965702 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316330535903) ^ 546006 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1046356766341370873006417 : Nat.Prime 1046356766341370873006417 := by
  apply lucas_primality 1046356766341370873006417 (3 : ZMod 1046356766341370873006417)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2447, 1), (11537861, 1), (2316330535903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2447, 1), (11537861, 1), (2316330535903, 1)] : List FactorBlock).map factorBlockValue).prod = 1046356766341370873006417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_2447
      · exact prime_nonG_11537861
      · exact prime_nonG_2316330535903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1046356766341370873006417) ^ 523178383170685436503208 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1046356766341370873006417) ^ 427607996052869175728 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1046356766341370873006417) ^ 90688973141674256 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1046356766341370873006417) ^ 451730333872 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_35153003 : Nat.Prime 35153003 := by
  apply lucas_primality 35153003 (2 : ZMod 35153003)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (925079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (925079, 1)] : List FactorBlock).map factorBlockValue).prod = 35153003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_19
      · exact prime_nonG_925079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35153003) ^ 17576501 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35153003) ^ 1850158 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35153003) ^ 38 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_84277243 : Nat.Prime 84277243 := by
  apply lucas_primality 84277243 (2 : ZMod 84277243)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (668867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (668867, 1)] : List FactorBlock).map factorBlockValue).prod = 84277243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_668867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84277243) ^ 42138621 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 28092414 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 12039606 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 126 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_307235059 : Nat.Prime 307235059 := by
  apply lucas_primality 307235059 (3 : ZMod 307235059)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (23, 1), (41, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (23, 1), (41, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod = 307235059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_13
      · exact prime_nonG_23
      · exact prime_nonG_41
      · exact prime_nonG_4177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 307235059) ^ 153617529 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 102411686 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 23633466 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 13358046 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 7493538 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 73554 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_1820428050799897417896023 : Nat.Prime 1820428050799897417896023 := by
  apply lucas_primality 1820428050799897417896023 (5 : ZMod 1820428050799897417896023)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (35153003, 1), (84277243, 1), (307235059, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (35153003, 1), (84277243, 1), (307235059, 1)] : List FactorBlock).map factorBlockValue).prod = 1820428050799897417896023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_35153003
      · exact prime_nonG_84277243
      · exact prime_nonG_307235059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1820428050799897417896023) ^ 910214025399948708948011 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 51785847450924674 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 21600469901464354 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 5925196352021458 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_52657181 : Nat.Prime 52657181 := by
  apply lucas_primality 52657181 (3 : ZMod 52657181)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (2632859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (2632859, 1)] : List FactorBlock).map factorBlockValue).prod = 52657181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_5
      · exact prime_nonG_2632859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52657181) ^ 26328590 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52657181) ^ 10531436 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52657181) ^ 20 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_67049863 : Nat.Prime 67049863 := by
  apply lucas_primality 67049863 (5 : ZMod 67049863)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (1015907, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (1015907, 1)] : List FactorBlock).map factorBlockValue).prod = 67049863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11
      · exact prime_nonG_1015907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67049863) ^ 33524931 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67049863) ^ 22349954 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67049863) ^ 6095442 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 67049863) ^ 66 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_485038708943 : Nat.Prime 485038708943 := by
  apply lucas_primality 485038708943 (5 : ZMod 485038708943)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3617, 1), (67049863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3617, 1), (67049863, 1)] : List FactorBlock).map factorBlockValue).prod = 485038708943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3617
      · exact prime_nonG_67049863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 485038708943) ^ 242519354471 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 485038708943) ^ 134099726 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 485038708943) ^ 7234 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_3449076809376142757731687 : Nat.Prime 3449076809376142757731687 := by
  apply lucas_primality 3449076809376142757731687 (5 : ZMod 3449076809376142757731687)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (71, 1), (317, 1), (52657181, 1), (485038708943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (71, 1), (317, 1), (52657181, 1), (485038708943, 1)] : List FactorBlock).map factorBlockValue).prod = 3449076809376142757731687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_71
      · exact prime_nonG_317
      · exact prime_nonG_52657181
      · exact prime_nonG_485038708943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3449076809376142757731687) ^ 1724538404688071378865843 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3449076809376142757731687) ^ 1149692269792047585910562 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3449076809376142757731687) ^ 48578546610931588137066 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3449076809376142757731687) ^ 10880368483836412484958 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3449076809376142757731687) ^ 65500597333080606 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3449076809376142757731687) ^ 7110931036602 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_71800742784079 : Nat.Prime 71800742784079 := by
  apply lucas_primality 71800742784079 (3 : ZMod 71800742784079)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (11, 1), (53, 1), (6949, 1), (140659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (11, 1), (53, 1), (6949, 1), (140659, 1)] : List FactorBlock).map factorBlockValue).prod = 71800742784079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_53
      · exact prime_nonG_6949
      · exact prime_nonG_140659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 71800742784079) ^ 35900371392039 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 23933580928026 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 10257248969154 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 6527340253098 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 1354730995926 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 10332528822 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 510459642 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_281284292307138799873 : Nat.Prime 281284292307138799873 := by
  apply lucas_primality 281284292307138799873 (7 : ZMod 281284292307138799873)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5101, 1), (71800742784079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5101, 1), (71800742784079, 1)] : List FactorBlock).map factorBlockValue).prod = 281284292307138799873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5101
      · exact prime_nonG_71800742784079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 281284292307138799873) ^ 140642146153569399936 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 93761430769046266624 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 55142970458172672 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 3917568 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_8498723607767891699362823 : Nat.Prime 8498723607767891699362823 := by
  apply lucas_primality 8498723607767891699362823 (5 : ZMod 8498723607767891699362823)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (15107, 1), (281284292307138799873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (15107, 1), (281284292307138799873, 1)] : List FactorBlock).map factorBlockValue).prod = 8498723607767891699362823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_15107
      · exact prime_nonG_281284292307138799873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8498723607767891699362823) ^ 4249361803883945849681411 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8498723607767891699362823) ^ 562568584614277599746 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8498723607767891699362823) ^ 30214 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_464334046364003489 : Nat.Prime 464334046364003489 := by
  apply lucas_primality 464334046364003489 (3 : ZMod 464334046364003489)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (175691, 1), (186869, 1), (441971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (175691, 1), (186869, 1), (441971, 1)] : List FactorBlock).map factorBlockValue).prod = 464334046364003489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_175691
      · exact prime_nonG_186869
      · exact prime_nonG_441971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 464334046364003489) ^ 232167023182001744 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 464334046364003489) ^ 2642901721568 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 464334046364003489) ^ 2484810462752 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (3 : ZMod 464334046364003489) ^ 1050598447328 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_9416284917633097705842703 : Nat.Prime 9416284917633097705842703 := by
  apply lucas_primality 9416284917633097705842703 (6 : ZMod 9416284917633097705842703)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (177887, 1), (464334046364003489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (177887, 1), (464334046364003489, 1)] : List FactorBlock).map factorBlockValue).prod = 9416284917633097705842703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_19
      · exact prime_nonG_177887
      · exact prime_nonG_464334046364003489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9416284917633097705842703) ^ 4708142458816548852921351 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9416284917633097705842703) ^ 3138761639211032568614234 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9416284917633097705842703) ^ 495593943033320931886458 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9416284917633097705842703) ^ 52934081285496397746 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9416284917633097705842703) ^ 20279118 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_3616901
      · exact prime_nonG_5004841
      · exact prime_nonG_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_97
      · exact prime_nonG_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_120913658601425004631843801 : Nat.Prime 120913658601425004631843801 := by
  apply lucas_primality 120913658601425004631843801 (55 : ZMod 120913658601425004631843801)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 5), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 5), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 120913658601425004631843801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (55 : ZMod 120913658601425004631843801) ^ 60456829300712502315921900 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 40304552867141668210614600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 24182731720285000926368760 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 17273379800203572090263400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 9301050661648077279372600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 7112568153025000272461400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 6363876768496052875360200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 5257115591366304549210600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 4169436503497413952822200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 3900440600045967891349800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 3267936718957432557617400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 2949113624425000112971800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 2811945548870348944926600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 2572631034072872438975400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 2281389784932547257204600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 2049384044091949231048200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (55 : ZMod 120913658601425004631843801) ^ 1982191124613524666095800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_126671451868159528661931601 : Nat.Prime 126671451868159528661931601 := by
  apply lucas_primality 126671451868159528661931601 (89 : ZMod 126671451868159528661931601)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 126671451868159528661931601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 126671451868159528661931601) ^ 63335725934079764330965800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 42223817289386509553977200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 25334290373631905732386320 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 18095921695451361237418800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 11515586533469048060175600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 9743957836012271435533200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 7451261874597619333054800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 6666918519376817297996400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 5507454429050414289649200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 4367981098902052712480400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 4086175866714823505223600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 3423552753193500774646800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 3089547606540476308827600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 2945847717864175085161200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 2695137273790628269402800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 2390027393738859031357200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 2146973760477280146812400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (89 : ZMod 126671451868159528661931601) ^ 2076581178166549650195600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_131362987122535807501262401 : Nat.Prime 131362987122535807501262401 := by
  apply lucas_primality 131362987122535807501262401 (71 : ZMod 131362987122535807501262401)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 131362987122535807501262401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 131362987122535807501262401) ^ 65681493561267903750631200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 43787662374178602500420800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 26272597424507161500252480 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 18766141017505115357323200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 11942089738412346136478400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 10104845163271985192404800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 7727234536619753382427200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 6913841427501884605329600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 5711434222718948152228800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4529758176639165775905600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4237515713630187338750400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3550351003311778581115200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3203975295671605061006400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3054953188896181569796800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2794957172819910797899200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2478546926840298254740800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2226491307161623855953600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2153491592172718155758400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_141872026092338672101363393 : Nat.Prime 141872026092338672101363393 := by
  apply lucas_primality 141872026092338672101363393 (5 : ZMod 141872026092338672101363393)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 141872026092338672101363393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141872026092338672101363393) ^ 70936013046169336050681696 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 47290675364112890700454464 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 20267432298905524585909056 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 12897456917485333827396672 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 10913232776333744007797184 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 8345413299549333653021376 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 7466948741702035373755968 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 6168348960536464004407104 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 4892138830770299037978048 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 4576516970720602325850432 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 3834379083576720867604416 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 3460293319325333465886912 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 3299349444007876095380544 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 3018553746645503661731136 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 2676830680987522115120064 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 2404610611734553764429888 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (5 : ZMod 141872026092338672101363393) ^ 2325770919546535608219072 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_204623114556257700146197201 : Nat.Prime 204623114556257700146197201 := by
  apply lucas_primality 204623114556257700146197201 (71 : ZMod 204623114556257700146197201)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 5), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 5), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 204623114556257700146197201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 204623114556257700146197201) ^ 102311557278128850073098600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 68207704852085900048732400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 40924622911251540029239440 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 29231873508036814306599600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 18602101323296154558745200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 12036653797426923538011600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 10769637608224089481378800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 8896657154619900006356400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 7055969467457162074006800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 6600745630847022585361200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 5530354447466424328275600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 4990807672103846345029200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 4758677082703667445260400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 4353683288431014896727600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 3860813482193541512192400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 3468188382309452544850800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (71 : ZMod 204623114556257700146197201) ^ 3354477287807503281085200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_208635332488733341325534401 : Nat.Prime 208635332488733341325534401 := by
  apply lucas_primality 208635332488733341325534401 (79 : ZMod 208635332488733341325534401)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 208635332488733341325534401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 208635332488733341325534401) ^ 104317666244366670662767200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 69545110829577780441844800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 41727066497746668265106880 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 29805047498390477332219200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 18966848408066667393230400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 16048871729902564717348800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 10980806973091228490817600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 9071101412553623535892800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 7194321809956322114673600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 6730172015765591655662400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5638792769965765981771200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5088666646066666861598400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4851984476482170728500800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4439049627419858326075200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3936515707334591345764800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3536192076080226124161600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3420251352274317070910400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 272830819408343600194929601) ^ 136415409704171800097464800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 90943606469447866731643200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 54566163881668720038985920 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 38975831344049085742132800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 24802801764394872744993600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 16048871729902564717348800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 14359516810965452641838400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 11862209539493200008475200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 9407959289942882765342400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 8800994174462696780481600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 7373805929955232437700800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6654410229471795126705600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6344902776938223260347200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5804911051241353195636800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5147751309591388682923200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4624251176412603393134400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4472636383743337708113600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_17
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem prime_nonG_625905997466200023976603201 : Nat.Prime 625905997466200023976603201 := by
  apply lucas_primality 625905997466200023976603201 (79 : ZMod 625905997466200023976603201)
  · rw [← nonGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 625905997466200023976603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_nonG_2
      · exact prime_nonG_3
      · exact prime_nonG_5
      · exact prime_nonG_7
      · exact prime_nonG_11
      · exact prime_nonG_13
      · exact prime_nonG_19
      · exact prime_nonG_23
      · exact prime_nonG_29
      · exact prime_nonG_31
      · exact prime_nonG_37
      · exact prime_nonG_41
      · exact prime_nonG_43
      · exact prime_nonG_47
      · exact prime_nonG_53
      · exact prime_nonG_59
      · exact prime_nonG_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 625905997466200023976603201) ^ 312952998733100011988301600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 208635332488733341325534400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 125181199493240004795320640 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 89415142495171431996657600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 56900545224200002179691200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 48146615189707694152046400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 32942420919273685472452800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 27213304237660870607678400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 21582965429868966344020800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 20190516047296774966987200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 16916378309897297945313600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 15265999938200000584795200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 14555953429446512185502400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 13317148882259574978225600 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 11809547122003774037294400 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10608576228240678372484800 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10260754056822951212731200 ≠ 1
      rw [← nonGFastPow_eq_pow]
      decide

private theorem phi_nonG_10640401956925400407602254390 : Nat.totient 10640401956925400407602254390 = 4218495643099627772217530496 := by
  rw [← show ((([(2, 1), (5, 1), (113, 1), (9416284917633097705842703, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254390 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_113, prime_nonG_9416284917633097705842703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254391 : Nat.totient 10640401956925400407602254391 = 7037743253086888660617352704 := by
  rw [← show ((([(3, 2), (127, 1), (4597709, 1), (5054317, 1), (400597142329, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254391 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_127, prime_nonG_4597709, prime_nonG_5054317, prime_nonG_400597142329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254392 : Nat.totient 10640401956925400407602254392 = 5320199545495690204720846944 := by
  rw [← show ((([(2, 3), (3712717, 1), (358241752499766357347, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254392 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3712717, prime_nonG_358241752499766357347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254393 : Nat.totient 10640401956925400407602254393 = 9120342749831198562396891600 := by
  rw [← show ((([(7, 1), (5181151, 1), (374221343, 1), (783980375743, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254393 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_7, prime_nonG_5181151, prime_nonG_374221343, prime_nonG_783980375743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254394 : Nat.totient 10640401956925400407602254394 = 3526986122977194665466249600 := by
  rw [← show ((([(2, 1), (3, 1), (179, 1), (6442882141, 1), (1537706910526441, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254394 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_179, prime_nonG_6442882141, prime_nonG_1537706910526441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254395 : Nat.totient 10640401956925400407602254395 = 8498525258302815755050874304 := by
  rw [← show ((([(5, 1), (617, 1), (3449076809376142757731687, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254395 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_617, prime_nonG_3449076809376142757731687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254396 : Nat.totient 10640401956925400407602254396 = 5303203531247164420402400928 := by
  rw [← show ((([(2, 2), (313, 1), (8498723607767891699362823, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254396 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_313, prime_nonG_8498723607767891699362823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254397 : Nat.totient 10640401956925400407602254397 = 7091792231120772871953438720 := by
  rw [← show ((([(3, 1), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254397 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_3923, prime_nonG_8197093, prime_nonG_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254398 : Nat.totient 10640401956925400407602254398 = 5252826494092212734777638560 := by
  rw [← show ((([(2, 1), (79, 1), (189067, 1), (2202311, 1), (161735950924213, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254398 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_79, prime_nonG_189067, prime_nonG_2202311, prime_nonG_161735950924213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254399 : Nat.totient 10640401956925400407602254399 = 10530420468134277805495879680 := by
  rw [← show ((([(97, 1), (36749, 1), (160512643, 1), (18596513447881, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254399 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_97, prime_nonG_36749, prime_nonG_160512643, prime_nonG_18596513447881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254400 : Nat.totient 10640401956925400407602254400 = 1400142316134245754470400000 := by
  rw [← show ((([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_5, prime_nonG_7, prime_nonG_11, prime_nonG_13, prime_nonG_17, prime_nonG_19, prime_nonG_23, prime_nonG_29, prime_nonG_31, prime_nonG_37, prime_nonG_41, prime_nonG_43, prime_nonG_47, prime_nonG_53, prime_nonG_59, prime_nonG_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254401 : Nat.totient 10640401956925400407602254401 = 10604086591884699382320335152 := by
  rw [← show ((([(293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_293, prime_nonG_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254402 : Nat.totient 10640401956925400407602254402 = 5318202365131640153167468800 := by
  rw [← show ((([(2, 1), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_2663, prime_nonG_9063547, prime_nonG_26126021, prime_nonG_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254403 : Nat.totient 10640401956925400407602254403 = 7093601304383813978677452200 := by
  rw [← show ((([(3, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_30429025931, prime_nonG_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254404 : Nat.totient 10640401956925400407602254404 = 5318229584840440428642564096 := by
  rw [← show ((([(2, 2), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3137, prime_nonG_19309, prime_nonG_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254405 : Nat.totient 10640401956925400407602254405 = 8509511244484644338548800000 := by
  rw [← show ((([(5, 1), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_3181, prime_nonG_73571, prime_nonG_455881, prime_nonG_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254406 : Nat.totient 10640401956925400407602254406 = 3546331617394483884577175040 := by
  rw [← show ((([(2, 1), (3, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_8233, prime_nonG_93811, prime_nonG_8274073, prime_nonG_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254407 : Nat.totient 10640401956925400407602254407 = 8983470229083015603078075264 := by
  rw [← show ((([(7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_7, prime_nonG_67, prime_nonG_12583, prime_nonG_277259, prime_nonG_2674733, prime_nonG_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254408 : Nat.totient 10640401956925400407602254408 = 5313927265543310069616468480 := by
  rw [← show ((([(2, 3), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_919, prime_nonG_11257, prime_nonG_425291, prime_nonG_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254409 : Nat.totient 10640401956925400407602254409 = 7023328967119773837005857152 := by
  rw [← show ((([(3, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_103, prime_nonG_5009, prime_nonG_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254410 : Nat.totient 10640401956925400407602254410 = 4218215795169768351509667840 := by
  rw [← show ((([(2, 1), (5, 1), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_139, prime_nonG_577, prime_nonG_2303321, prime_nonG_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254411 : Nat.totient 10640401956925400407602254411 = 9608014555607977865373822720 := by
  rw [← show ((([(11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_11, prime_nonG_149, prime_nonG_60793, prime_nonG_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254412 : Nat.totient 10640401956925400407602254412 = 3540123320806535402535321600 := by
  rw [← show ((([(2, 2), (3, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_769, prime_nonG_2143, prime_nonG_8597, prime_nonG_9792301, prime_nonG_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254413 : Nat.totient 10640401956925400407602254413 = 9821054601886138571278184448 := by
  rw [← show ((([(13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_13, prime_nonG_11489, prime_nonG_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254414 : Nat.totient 10640401956925400407602254414 = 4543709550820339358140577280 := by
  rw [← show ((([(2, 1), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_7, prime_nonG_277, prime_nonG_6810796141, prime_nonG_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254415 : Nat.totient 10640401956925400407602254415 = 5647033928394127664705157120 := by
  rw [← show ((([(3, 1), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_5, prime_nonG_281, prime_nonG_739, prime_nonG_3540386347, prime_nonG_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254416 : Nat.totient 10640401956925400407602254416 = 5319995665276376187981400320 := by
  rw [← show ((([(2, 4), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_25913, prime_nonG_1731666887, prime_nonG_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254417 : Nat.totient 10640401956925400407602254417 = 10014495959459200383625651200 := by
  rw [← show ((([(17, 1), (625905997466200023976603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_17, prime_nonG_625905997466200023976603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254418 : Nat.totient 10640401956925400407602254418 = 3546800649407473472293236600 := by
  rw [← show ((([(2, 1), (3, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_1222615931, prime_nonG_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254419 : Nat.totient 10640401956925400407602254419 = 10077624661318833928783818240 := by
  rw [← show ((([(19, 1), (3691, 1), (401987, 1), (377440396466729153, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_19, prime_nonG_3691, prime_nonG_401987, prime_nonG_377440396466729153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254420 : Nat.totient 10640401956925400407602254420 = 4197493664464101379985682432 := by
  rw [← show ((([(2, 2), (5, 1), (73, 1), (11953, 1), (339907, 1), (1793775758729587, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_73, prime_nonG_11953, prime_nonG_339907, prime_nonG_1793775758729587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254421 : Nat.totient 10640401956925400407602254421 = 6071866087062023771393572416 := by
  rw [← show ((([(3, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_7, prime_nonG_727, prime_nonG_40346827, prime_nonG_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254422 : Nat.totient 10640401956925400407602254422 = 4832553606849228785230786080 := by
  rw [← show ((([(2, 1), (11, 1), (1277, 1), (23539, 1), (16090014941653837367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_11, prime_nonG_1277, prime_nonG_23539, prime_nonG_16090014941653837367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254423 : Nat.totient 10640401956925400407602254423 = 10170500748584318455300803288 := by
  rw [← show ((([(23, 1), (1399, 1), (330683468220325089585799, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_23, prime_nonG_1399, prime_nonG_330683468220325089585799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254424 : Nat.totient 10640401956925400407602254424 = 3537200714323009588295639040 := by
  rw [← show ((([(2, 3), (3, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_373, prime_nonG_55249, prime_nonG_157429, prime_nonG_773027, prime_nonG_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254425 : Nat.totient 10640401956925400407602254425 = 8512320851560884454764286080 := by
  rw [← show ((([(5, 2), (12759209, 1), (181957939, 1), (183325663427, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_12759209, prime_nonG_181957939, prime_nonG_183325663427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254426 : Nat.totient 10640401956925400407602254426 = 4902353307779984528415652800 := by
  rw [← show ((([(2, 1), (13, 1), (571, 1), (11213231, 1), (12829519, 1), (4982042579, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_13, prime_nonG_571, prime_nonG_11213231, prime_nonG_12829519, prime_nonG_4982042579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254427 : Nat.totient 10640401956925400407602254427 = 7093601304616933605068169600 := by
  rw [← show ((([(3, 3), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254428 : Nat.totient 10640401956925400407602254428 = 4559952171097207786738704048 := by
  rw [← show ((([(2, 2), (7, 1), (20719, 1), (18341346377937090882079, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_7, prime_nonG_20719, prime_nonG_18341346377937090882079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254429 : Nat.totient 10640401956925400407602254429 = 10250084863337765202739765440 := by
  rw [← show ((([(29, 1), (439, 1), (2284423, 1), (63388891, 1), (5771727763, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_29, prime_nonG_439, prime_nonG_2284423, prime_nonG_63388891, prime_nonG_5771727763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254430 : Nat.totient 10640401956925400407602254430 = 2837424804828157195835697536 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_5, prime_nonG_180533, prime_nonG_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254431 : Nat.totient 10640401956925400407602254431 = 10154983338251816625983743200 := by
  rw [← show ((([(31, 1), (83, 1), (563, 1), (210739, 1), (34854988069713571, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_31, prime_nonG_83, prime_nonG_563, prime_nonG_210739, prime_nonG_34854988069713571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254432 : Nat.totient 10640401956925400407602254432 = 5310219522423349865658654720 := by
  rw [← show ((([(2, 5), (541, 1), (36017, 1), (4054368629, 1), (4209010627, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_541, prime_nonG_36017, prime_nonG_4054368629, prime_nonG_4209010627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254433 : Nat.totient 10640401956925400407602254433 = 6447337744303139910336514560 := by
  rw [← show ((([(3, 1), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_11, prime_nonG_4637, prime_nonG_2076644077, prime_nonG_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254434 : Nat.totient 10640401956925400407602254434 = 4936261155325393524606976000 := by
  rw [← show ((([(2, 1), (17, 1), (71, 1), (15401, 1), (34847, 1), (8213087550976673, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_17, prime_nonG_71, prime_nonG_15401, prime_nonG_34847, prime_nonG_8213087550976673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254435 : Nat.totient 10640401956925400407602254435 = 7252585354386791312897751648 := by
  rw [← show ((([(5, 1), (7, 1), (167, 1), (1820428050799897417896023, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_7, prime_nonG_167, prime_nonG_1820428050799897417896023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254436 : Nat.totient 10640401956925400407602254436 = 3546800482854297447975573504 := by
  rw [← show ((([(2, 2), (3, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_20930737, prime_nonG_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254437 : Nat.totient 10640401956925400407602254437 = 10352823525456369302110536144 := by
  rw [← show ((([(37, 1), (51564258659, 1), (5577088447446539, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_37, prime_nonG_51564258659, prime_nonG_5577088447446539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254438 : Nat.totient 10640401956925400407602254438 = 4992532812058498458840617184 := by
  rw [← show ((([(2, 1), (19, 1), (107, 1), (9029, 1), (289835118837045663367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_19, prime_nonG_107, prime_nonG_9029, prime_nonG_289835118837045663367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254439 : Nat.totient 10640401956925400407602254439 = 6547939665800246404678310400 := by
  rw [← show ((([(3, 1), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_13, prime_nonG_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254440 : Nat.totient 10640401956925400407602254440 = 4252612757866214172964454400 := by
  rw [← show ((([(2, 3), (5, 1), (2239, 1), (2609, 1), (276707, 1), (4175273, 1), (39415301, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_2239, prime_nonG_2609, prime_nonG_276707, prime_nonG_4175273, prime_nonG_39415301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254441 : Nat.totient 10640401956925400407602254441 = 10380420891069443284477252480 := by
  rw [← show ((([(41, 1), (22613, 1), (11476672663927829564477, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_41, prime_nonG_22613, prime_nonG_11476672663927829564477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254442 : Nat.totient 10640401956925400407602254442 = 3040099278051909269450822400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_7, prime_nonG_339389, prime_nonG_545911, prime_nonG_2940799, prime_nonG_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254443 : Nat.totient 10640401956925400407602254443 = 10317030441624254370494880576 := by
  rw [← show ((([(43, 1), (137, 1), (173827, 1), (10390866777165714899, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_43, prime_nonG_137, prime_nonG_173827, prime_nonG_10390866777165714899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254444 : Nat.totient 10640401956925400407602254444 = 4836453934982613310683408960 := by
  rw [← show ((([(2, 2), (11, 1), (55807, 1), (842077, 1), (5145941864693659, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_11, prime_nonG_55807, prime_nonG_842077, prime_nonG_5145941864693659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254445 : Nat.totient 10640401956925400407602254445 = 5674881034629409990943511648 := by
  rw [← show ((([(3, 2), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_5, prime_nonG_626080687, prime_nonG_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254446 : Nat.totient 10640401956925400407602254446 = 5060772489710661928705401120 := by
  rw [← show ((([(2, 1), (23, 1), (181, 1), (560911155227, 1), (2278387297223, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_23, prime_nonG_181, prime_nonG_560911155227, prime_nonG_2278387297223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254447 : Nat.totient 10640401956925400407602254447 = 10364270466360158957642977440 := by
  rw [← show ((([(47, 1), (211, 1), (26959, 1), (39799163342195208949, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_47, prime_nonG_211, prime_nonG_26959, prime_nonG_39799163342195208949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254448 : Nat.totient 10640401956925400407602254448 = 3515752135273223057525913600 := by
  rw [← show ((([(2, 4), (3, 1), (197, 1), (271, 1), (152441, 1), (27238268144131903, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_197, prime_nonG_271, prime_nonG_152441, prime_nonG_27238268144131903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254449 : Nat.totient 10640401956925400407602254449 = 9120344511972946416011564640 := by
  rw [← show ((([(7, 3), (404727353, 1), (76648093634890031, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_7, prime_nonG_404727353, prime_nonG_76648093634890031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254450 : Nat.totient 10640401956925400407602254450 = 4255917500372671854063040320 := by
  rw [← show ((([(2, 1), (5, 2), (17683, 1), (2103139, 1), (7587443, 1), (754168979, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_17683, prime_nonG_2103139, prime_nonG_7587443, prime_nonG_754168979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254451 : Nat.totient 10640401956925400407602254451 = 6676330639639466922417100800 := by
  rw [← show ((([(3, 1), (17, 1), (208635332488733341325534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_17, prime_nonG_208635332488733341325534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254452 : Nat.totient 10640401956925400407602254452 = 4910954749350184803508732800 := by
  rw [← show ((([(2, 2), (13, 1), (204623114556257700146197201, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_13, prime_nonG_204623114556257700146197201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254453 : Nat.totient 10640401956925400407602254453 = 10389451368895328335622889600 := by
  rw [← show ((([(53, 1), (307, 1), (643, 1), (1017027781389477047401, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_53, prime_nonG_307, prime_nonG_643, prime_nonG_1017027781389477047401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254454 : Nat.totient 10640401956925400407602254454 = 3538050364262235850746992064 := by
  rw [← show ((([(2, 1), (3, 3), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_409, prime_nonG_45127, prime_nonG_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254455 : Nat.totient 10640401956925400407602254455 = 7738310208859176547348176000 := by
  rw [← show ((([(5, 1), (11, 3), (52859, 1), (441101, 1), (68572974676279, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_11, prime_nonG_52859, prime_nonG_441101, prime_nonG_68572974676279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254456 : Nat.totient 10640401956925400407602254456 = 4559969979525079866188583648 := by
  rw [← show ((([(2, 3), (7, 1), (22543, 1), (8428655360965235017207, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_7, prime_nonG_22543, prime_nonG_8428655360965235017207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254457 : Nat.totient 10640401956925400407602254457 = 6720253846657303228368422544 := by
  rw [← show ((([(3, 1), (19, 1), (321935599, 1), (579848016567285199, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_19, prime_nonG_321935599, prime_nonG_579848016567285199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254458 : Nat.totient 10640401956925400407602254458 = 5136745772259192604307594800 := by
  rw [← show ((([(2, 1), (29, 1), (103524837131, 1), (1772088816925571, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_29, prime_nonG_103524837131, prime_nonG_1772088816925571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254459 : Nat.totient 10640401956925400407602254459 = 10459920214689681099325067520 := by
  rw [← show ((([(59, 1), (76943, 1), (13493024417, 1), (173711112271, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_59, prime_nonG_76943, prime_nonG_13493024417, prime_nonG_173711112271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254460 : Nat.totient 10640401956925400407602254460 = 2819022944168352897362619648 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (157, 1), (8179, 1), (138104211745804923847, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_5, prime_nonG_157, prime_nonG_8179, prime_nonG_138104211745804923847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254461 : Nat.totient 10640401956925400407602254461 = 10465964865741439322103467520 := by
  rw [← show ((([(61, 1), (2771233, 1), (21119159, 1), (2980427332583, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_61, prime_nonG_2771233, prime_nonG_21119159, prime_nonG_2980427332583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254462 : Nat.totient 10640401956925400407602254462 = 5148579983069422346021337600 := by
  rw [← show ((([(2, 1), (31, 1), (3207943, 1), (1314491287, 1), (40698836161, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_31, prime_nonG_3207943, prime_nonG_1314491287, prime_nonG_40698836161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254463 : Nat.totient 10640401956925400407602254463 = 6067040470806006810641517120 := by
  rw [← show ((([(3, 2), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_7, prime_nonG_461, prime_nonG_13492702567, prime_nonG_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254464 : Nat.totient 10640401956925400407602254464 = 5293466300178968041972968192 := by
  rw [← show ((([(2, 7), (199, 1), (417729348183315028564787, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_199, prime_nonG_417729348183315028564787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254465 : Nat.totient 10640401956925400407602254465 = 7857527598858556963499098944 := by
  rw [← show ((([(5, 1), (13, 2), (77269038083, 1), (162965554863959, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_13, prime_nonG_77269038083, prime_nonG_162965554863959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254466 : Nat.totient 10640401956925400407602254466 = 3222903257812941371005513040 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (2207, 1), (73048577919604292180543, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_11, prime_nonG_2207, prime_nonG_73048577919604292180543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254467 : Nat.totient 10640401956925400407602254467 = 10640401956780578050090169296 := by
  rw [← show ((([(73472131913, 1), (144822284039953259, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_73472131913, prime_nonG_144822284039953259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254468 : Nat.totient 10640401956925400407602254468 = 5007218580406714652733841920 := by
  rw [← show ((([(2, 2), (17, 2), (170327, 1), (4946199949, 1), (10925593411, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_17, prime_nonG_170327, prime_nonG_4946199949, prime_nonG_10925593411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254469 : Nat.totient 10640401956925400407602254469 = 6785183849662927308889916528 := by
  rw [← show ((([(3, 1), (23, 1), (979501163, 1), (157435978474087427, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_23, prime_nonG_979501163, prime_nonG_157435978474087427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254470 : Nat.totient 10640401956925400407602254470 = 3599740627569076104288675072 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (89, 1), (487, 1), (3507042480718718925647, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_7, prime_nonG_89, prime_nonG_487, prime_nonG_3507042480718718925647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254471 : Nat.totient 10640401956925400407602254471 = 10639269635953964947779964320 := by
  rw [← show ((([(9397, 1), (5489884663, 1), (206255523187661, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_9397, prime_nonG_5489884663, prime_nonG_206255523187661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254472 : Nat.totient 10640401956925400407602254472 = 3528231002875955915514904320 := by
  rw [← show ((([(2, 3), (3, 2), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_191, prime_nonG_282045737, prime_nonG_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254473 : Nat.totient 10640401956925400407602254473 = 10639355600159059036729237888 := by
  rw [← show ((([(10169, 1), (1046356766341370873006417, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_10169, prime_nonG_1046356766341370873006417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254474 : Nat.totient 10640401956925400407602254474 = 5093769440860836855420026880 := by
  rw [← show ((([(2, 1), (37, 1), (67, 1), (1123, 1), (7321, 1), (34913, 1), (7476772742657, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_37, prime_nonG_67, prime_nonG_1123, prime_nonG_7321, prime_nonG_34913, prime_nonG_7476772742657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254475 : Nat.totient 10640401956925400407602254475 = 5674881043693546884054535680 := by
  rw [← show ((([(3, 1), (5, 2), (141872026092338672101363393, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_5, prime_nonG_141872026092338672101363393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254476 : Nat.totient 10640401956925400407602254476 = 5040190275149402966878066944 := by
  rw [← show ((([(2, 2), (19, 1), (40161049, 1), (3486096414137817049, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_19, prime_nonG_40161049, prime_nonG_3486096414137817049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254477 : Nat.totient 10640401956925400407602254477 = 8186269827735249010940836800 := by
  rw [← show ((([(7, 1), (11, 1), (79, 1), (44619727, 1), (87498511, 1), (448035727, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_7, prime_nonG_11, prime_nonG_79, prime_nonG_44619727, prime_nonG_87498511, prime_nonG_448035727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254478 : Nat.totient 10640401956925400407602254478 = 3264695130493371152484910080 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (353, 1), (9879116647, 1), (39117456919511, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_13, prime_nonG_353, prime_nonG_9879116647, prime_nonG_39117456919511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254479 : Nat.totient 10640401956925400407602254479 = 10640401840875553112265828984 := by
  rw [← show ((([(91688203, 1), (116049847295244737293, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_91688203, prime_nonG_116049847295244737293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254480 : Nat.totient 10640401956925400407602254480 = 4242734408031703215679488000 := by
  rw [← show ((([(2, 4), (5, 1), (317, 1), (152270997001, 1), (2755444030193, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_5, prime_nonG_317, prime_nonG_152270997001, prime_nonG_2755444030193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254481 : Nat.totient 10640401956925400407602254481 = 7093601304616933605068169600 := by
  rw [← show ((([(3, 4), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254482 : Nat.totient 10640401956925400407602254482 = 5167942492290214850893824000 := by
  rw [← show ((([(2, 1), (41, 1), (233, 1), (26539, 1), (212453, 1), (3044831, 1), (32439761, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_41, prime_nonG_233, prime_nonG_26539, prime_nonG_212453, prime_nonG_3044831, prime_nonG_32439761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254483 : Nat.totient 10640401956925400407602254483 = 10637031468488293387383237000 := by
  rw [← show ((([(3163, 1), (1644991, 1), (2045009436082096151, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3163, prime_nonG_1644991, prime_nonG_2045009436082096151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254484 : Nat.totient 10640401956925400407602254484 = 3040114844835828687886358400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (126671451868159528661931601, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_3, prime_nonG_7, prime_nonG_126671451868159528661931601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254485 : Nat.totient 10640401956925400407602254485 = 8011585101286432887881299200 := by
  rw [← show ((([(5, 1), (17, 1), (686731, 1), (182285639490921488611, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_5, prime_nonG_17, prime_nonG_686731, prime_nonG_182285639490921488611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254486 : Nat.totient 10640401956925400407602254486 = 5196475373930210505624123264 := by
  rw [← show ((([(2, 1), (43, 1), (13596441737, 1), (9099851751182873, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_43, prime_nonG_13596441737, prime_nonG_9099851751182873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254487 : Nat.totient 10640401956925400407602254487 = 6777893828227209555635066880 := by
  rw [← show ((([(3, 1), (29, 1), (109, 1), (821, 1), (1366687199200543932209, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_3, prime_nonG_29, prime_nonG_109, prime_nonG_821, prime_nonG_1366687199200543932209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_nonG_10640401956925400407602254488 : Nat.totient 10640401956925400407602254488 = 4836546344057000185273752000 := by
  rw [← show ((([(2, 3), (11, 1), (120913658601425004631843801, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400407602254488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_nonG_2, prime_nonG_11, prime_nonG_120913658601425004631843801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NonG : certifiedKill 1 10640401956925400407602254389 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_nonG_10640401956925400407602254390, phi_nonG_10640401956925400407602254391, phi_nonG_10640401956925400407602254392,
    phi_nonG_10640401956925400407602254393, phi_nonG_10640401956925400407602254394, phi_nonG_10640401956925400407602254395,
    phi_nonG_10640401956925400407602254396, phi_nonG_10640401956925400407602254397, phi_nonG_10640401956925400407602254398,
    phi_nonG_10640401956925400407602254399, phi_nonG_10640401956925400407602254400, phi_nonG_10640401956925400407602254401,
    phi_nonG_10640401956925400407602254402, phi_nonG_10640401956925400407602254403, phi_nonG_10640401956925400407602254404,
    phi_nonG_10640401956925400407602254405, phi_nonG_10640401956925400407602254406, phi_nonG_10640401956925400407602254407,
    phi_nonG_10640401956925400407602254408, phi_nonG_10640401956925400407602254409, phi_nonG_10640401956925400407602254410,
    phi_nonG_10640401956925400407602254411, phi_nonG_10640401956925400407602254412, phi_nonG_10640401956925400407602254413,
    phi_nonG_10640401956925400407602254414, phi_nonG_10640401956925400407602254415, phi_nonG_10640401956925400407602254416,
    phi_nonG_10640401956925400407602254417, phi_nonG_10640401956925400407602254418, phi_nonG_10640401956925400407602254419,
    phi_nonG_10640401956925400407602254420, phi_nonG_10640401956925400407602254421, phi_nonG_10640401956925400407602254422,
    phi_nonG_10640401956925400407602254423, phi_nonG_10640401956925400407602254424, phi_nonG_10640401956925400407602254425,
    phi_nonG_10640401956925400407602254426, phi_nonG_10640401956925400407602254427, phi_nonG_10640401956925400407602254428,
    phi_nonG_10640401956925400407602254429, phi_nonG_10640401956925400407602254430, phi_nonG_10640401956925400407602254431,
    phi_nonG_10640401956925400407602254432, phi_nonG_10640401956925400407602254433, phi_nonG_10640401956925400407602254434,
    phi_nonG_10640401956925400407602254435, phi_nonG_10640401956925400407602254436, phi_nonG_10640401956925400407602254437,
    phi_nonG_10640401956925400407602254438, phi_nonG_10640401956925400407602254439, phi_nonG_10640401956925400407602254440,
    phi_nonG_10640401956925400407602254441, phi_nonG_10640401956925400407602254442, phi_nonG_10640401956925400407602254443,
    phi_nonG_10640401956925400407602254444, phi_nonG_10640401956925400407602254445, phi_nonG_10640401956925400407602254446,
    phi_nonG_10640401956925400407602254447, phi_nonG_10640401956925400407602254448, phi_nonG_10640401956925400407602254449,
    phi_nonG_10640401956925400407602254450, phi_nonG_10640401956925400407602254451, phi_nonG_10640401956925400407602254452,
    phi_nonG_10640401956925400407602254453, phi_nonG_10640401956925400407602254454, phi_nonG_10640401956925400407602254455,
    phi_nonG_10640401956925400407602254456, phi_nonG_10640401956925400407602254457, phi_nonG_10640401956925400407602254458,
    phi_nonG_10640401956925400407602254459, phi_nonG_10640401956925400407602254460, phi_nonG_10640401956925400407602254461,
    phi_nonG_10640401956925400407602254462, phi_nonG_10640401956925400407602254463, phi_nonG_10640401956925400407602254464,
    phi_nonG_10640401956925400407602254465, phi_nonG_10640401956925400407602254466, phi_nonG_10640401956925400407602254467,
    phi_nonG_10640401956925400407602254468, phi_nonG_10640401956925400407602254469, phi_nonG_10640401956925400407602254470,
    phi_nonG_10640401956925400407602254471, phi_nonG_10640401956925400407602254472, phi_nonG_10640401956925400407602254473,
    phi_nonG_10640401956925400407602254474, phi_nonG_10640401956925400407602254475, phi_nonG_10640401956925400407602254476,
    phi_nonG_10640401956925400407602254477, phi_nonG_10640401956925400407602254478, phi_nonG_10640401956925400407602254479,
    phi_nonG_10640401956925400407602254480, phi_nonG_10640401956925400407602254481, phi_nonG_10640401956925400407602254482,
    phi_nonG_10640401956925400407602254483, phi_nonG_10640401956925400407602254484, phi_nonG_10640401956925400407602254485,
    phi_nonG_10640401956925400407602254486, phi_nonG_10640401956925400407602254487, phi_nonG_10640401956925400407602254488]

end TotientTailPeriodKiller
end Erdos249257
