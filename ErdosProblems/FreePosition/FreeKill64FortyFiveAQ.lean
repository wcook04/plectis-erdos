import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyFiveAQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyFiveAQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyFiveAQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyFiveAQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyFiveAQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyFiveAQFastPow a n * fortyFiveAQFastPow a n * a
        else fortyFiveAQFastPow a n * fortyFiveAQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyFiveAQ_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyFiveAQ_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyFiveAQ_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyFiveAQ_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyFiveAQ_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyFiveAQ_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyFiveAQ_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyFiveAQ_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyFiveAQ_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyFiveAQ_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyFiveAQ_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyFiveAQ_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyFiveAQ_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyFiveAQ_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyFiveAQ_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyFiveAQ_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyFiveAQ_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyFiveAQ_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyFiveAQ_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyFiveAQ_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyFiveAQ_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyFiveAQ_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyFiveAQ_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyFiveAQ_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyFiveAQ_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyFiveAQ_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyFiveAQ_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyFiveAQ_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyFiveAQ_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyFiveAQ_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyFiveAQ_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyFiveAQ_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyFiveAQ_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyFiveAQ_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyFiveAQ_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyFiveAQ_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyFiveAQ_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyFiveAQ_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyFiveAQ_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyFiveAQ_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyFiveAQ_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortyFiveAQ_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyFiveAQ_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyFiveAQ_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyFiveAQ_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyFiveAQ_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyFiveAQ_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyFiveAQ_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyFiveAQ_241 : Nat.Prime 241 := by norm_num
private theorem prime_fortyFiveAQ_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyFiveAQ_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortyFiveAQ_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyFiveAQ_271 : Nat.Prime 271 := by norm_num
private theorem prime_fortyFiveAQ_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortyFiveAQ_281 : Nat.Prime 281 := by norm_num
private theorem prime_fortyFiveAQ_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyFiveAQ_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyFiveAQ_311 : Nat.Prime 311 := by norm_num
private theorem prime_fortyFiveAQ_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyFiveAQ_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyFiveAQ_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyFiveAQ_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyFiveAQ_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyFiveAQ_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyFiveAQ_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortyFiveAQ_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyFiveAQ_389 : Nat.Prime 389 := by norm_num
private theorem prime_fortyFiveAQ_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyFiveAQ_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortyFiveAQ_433 : Nat.Prime 433 := by norm_num
private theorem prime_fortyFiveAQ_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyFiveAQ_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortyFiveAQ_463 : Nat.Prime 463 := by norm_num
private theorem prime_fortyFiveAQ_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyFiveAQ_503 : Nat.Prime 503 := by norm_num
private theorem prime_fortyFiveAQ_521 : Nat.Prime 521 := by norm_num
private theorem prime_fortyFiveAQ_569 : Nat.Prime 569 := by norm_num
private theorem prime_fortyFiveAQ_571 : Nat.Prime 571 := by norm_num
private theorem prime_fortyFiveAQ_577 : Nat.Prime 577 := by norm_num
private theorem prime_fortyFiveAQ_587 : Nat.Prime 587 := by norm_num
private theorem prime_fortyFiveAQ_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyFiveAQ_607 : Nat.Prime 607 := by norm_num
private theorem prime_fortyFiveAQ_613 : Nat.Prime 613 := by norm_num
private theorem prime_fortyFiveAQ_619 : Nat.Prime 619 := by norm_num
private theorem prime_fortyFiveAQ_641 : Nat.Prime 641 := by norm_num
private theorem prime_fortyFiveAQ_661 : Nat.Prime 661 := by norm_num
private theorem prime_fortyFiveAQ_701 : Nat.Prime 701 := by norm_num
private theorem prime_fortyFiveAQ_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortyFiveAQ_739 : Nat.Prime 739 := by norm_num
private theorem prime_fortyFiveAQ_743 : Nat.Prime 743 := by norm_num
private theorem prime_fortyFiveAQ_761 : Nat.Prime 761 := by norm_num
private theorem prime_fortyFiveAQ_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyFiveAQ_787 : Nat.Prime 787 := by norm_num
private theorem prime_fortyFiveAQ_809 : Nat.Prime 809 := by norm_num
private theorem prime_fortyFiveAQ_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyFiveAQ_821 : Nat.Prime 821 := by norm_num
private theorem prime_fortyFiveAQ_827 : Nat.Prime 827 := by norm_num
private theorem prime_fortyFiveAQ_883 : Nat.Prime 883 := by norm_num
private theorem prime_fortyFiveAQ_887 : Nat.Prime 887 := by norm_num
private theorem prime_fortyFiveAQ_919 : Nat.Prime 919 := by norm_num
private theorem prime_fortyFiveAQ_947 : Nat.Prime 947 := by norm_num
private theorem prime_fortyFiveAQ_977 : Nat.Prime 977 := by norm_num
private theorem prime_fortyFiveAQ_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyFiveAQ_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fortyFiveAQ_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fortyFiveAQ_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fortyFiveAQ_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fortyFiveAQ_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_fortyFiveAQ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fortyFiveAQ_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortyFiveAQ_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortyFiveAQ_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fortyFiveAQ_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_fortyFiveAQ_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_fortyFiveAQ_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fortyFiveAQ_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_fortyFiveAQ_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_fortyFiveAQ_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyFiveAQ_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fortyFiveAQ_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_fortyFiveAQ_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyFiveAQ_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_fortyFiveAQ_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_fortyFiveAQ_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fortyFiveAQ_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_fortyFiveAQ_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_fortyFiveAQ_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_fortyFiveAQ_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_fortyFiveAQ_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fortyFiveAQ_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_fortyFiveAQ_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fortyFiveAQ_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_fortyFiveAQ_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_fortyFiveAQ_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_fortyFiveAQ_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_fortyFiveAQ_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fortyFiveAQ_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fortyFiveAQ_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_fortyFiveAQ_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_fortyFiveAQ_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_fortyFiveAQ_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_fortyFiveAQ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyFiveAQ_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_fortyFiveAQ_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_fortyFiveAQ_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_fortyFiveAQ_2749 : Nat.Prime 2749 := by norm_num
private theorem prime_fortyFiveAQ_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_fortyFiveAQ_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_fortyFiveAQ_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_fortyFiveAQ_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fortyFiveAQ_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_fortyFiveAQ_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_fortyFiveAQ_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_fortyFiveAQ_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_fortyFiveAQ_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_fortyFiveAQ_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_fortyFiveAQ_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_fortyFiveAQ_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_fortyFiveAQ_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_fortyFiveAQ_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_fortyFiveAQ_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_fortyFiveAQ_3931 : Nat.Prime 3931 := by norm_num
private theorem prime_fortyFiveAQ_3943 : Nat.Prime 3943 := by norm_num
private theorem prime_fortyFiveAQ_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_fortyFiveAQ_4073 : Nat.Prime 4073 := by norm_num
private theorem prime_fortyFiveAQ_4447 : Nat.Prime 4447 := by norm_num
private theorem prime_fortyFiveAQ_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_fortyFiveAQ_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_fortyFiveAQ_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_fortyFiveAQ_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_fortyFiveAQ_4871 : Nat.Prime 4871 := by norm_num
private theorem prime_fortyFiveAQ_4877 : Nat.Prime 4877 := by norm_num
private theorem prime_fortyFiveAQ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyFiveAQ_5023 : Nat.Prime 5023 := by norm_num
private theorem prime_fortyFiveAQ_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_fortyFiveAQ_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_fortyFiveAQ_5591 : Nat.Prime 5591 := by norm_num
private theorem prime_fortyFiveAQ_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_fortyFiveAQ_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fortyFiveAQ_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fortyFiveAQ_6473 : Nat.Prime 6473 := by norm_num
private theorem prime_fortyFiveAQ_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyFiveAQ_6827 : Nat.Prime 6827 := by norm_num
private theorem prime_fortyFiveAQ_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_fortyFiveAQ_7541 : Nat.Prime 7541 := by norm_num
private theorem prime_fortyFiveAQ_7621 : Nat.Prime 7621 := by norm_num
private theorem prime_fortyFiveAQ_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_fortyFiveAQ_7789 : Nat.Prime 7789 := by norm_num
private theorem prime_fortyFiveAQ_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_fortyFiveAQ_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fortyFiveAQ_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fortyFiveAQ_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fortyFiveAQ_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_fortyFiveAQ_9203 : Nat.Prime 9203 := by norm_num
private theorem prime_fortyFiveAQ_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_fortyFiveAQ_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_fortyFiveAQ_10627 : Nat.Prime 10627 := by norm_num
private theorem prime_fortyFiveAQ_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fortyFiveAQ_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_fortyFiveAQ_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_fortyFiveAQ_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_fortyFiveAQ_11801 : Nat.Prime 11801 := by norm_num
private theorem prime_fortyFiveAQ_11941 : Nat.Prime 11941 := by norm_num
private theorem prime_fortyFiveAQ_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_fortyFiveAQ_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_fortyFiveAQ_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_fortyFiveAQ_13339 : Nat.Prime 13339 := by norm_num
private theorem prime_fortyFiveAQ_13523 : Nat.Prime 13523 := by norm_num
private theorem prime_fortyFiveAQ_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_fortyFiveAQ_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_fortyFiveAQ_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_fortyFiveAQ_14869 : Nat.Prime 14869 := by norm_num
private theorem prime_fortyFiveAQ_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_fortyFiveAQ_15643 : Nat.Prime 15643 := by norm_num
private theorem prime_fortyFiveAQ_17581 : Nat.Prime 17581 := by norm_num
private theorem prime_fortyFiveAQ_17903 : Nat.Prime 17903 := by norm_num
private theorem prime_fortyFiveAQ_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_fortyFiveAQ_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_fortyFiveAQ_20101 : Nat.Prime 20101 := by norm_num
private theorem prime_fortyFiveAQ_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_fortyFiveAQ_23251 : Nat.Prime 23251 := by norm_num
private theorem prime_fortyFiveAQ_25183 : Nat.Prime 25183 := by norm_num
private theorem prime_fortyFiveAQ_25391 : Nat.Prime 25391 := by norm_num
private theorem prime_fortyFiveAQ_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_fortyFiveAQ_26921 : Nat.Prime 26921 := by norm_num
private theorem prime_fortyFiveAQ_27631 : Nat.Prime 27631 := by norm_num
private theorem prime_fortyFiveAQ_28517 : Nat.Prime 28517 := by norm_num
private theorem prime_fortyFiveAQ_28751 : Nat.Prime 28751 := by norm_num
private theorem prime_fortyFiveAQ_30109 : Nat.Prime 30109 := by norm_num
private theorem prime_fortyFiveAQ_31063 : Nat.Prime 31063 := by norm_num
private theorem prime_fortyFiveAQ_33641 : Nat.Prime 33641 := by norm_num
private theorem prime_fortyFiveAQ_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_fortyFiveAQ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyFiveAQ_36587 : Nat.Prime 36587 := by norm_num
private theorem prime_fortyFiveAQ_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_fortyFiveAQ_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyFiveAQ_40193 : Nat.Prime 40193 := by norm_num
private theorem prime_fortyFiveAQ_40351 : Nat.Prime 40351 := by norm_num
private theorem prime_fortyFiveAQ_48179 : Nat.Prime 48179 := by norm_num
private theorem prime_fortyFiveAQ_53441 : Nat.Prime 53441 := by norm_num
private theorem prime_fortyFiveAQ_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_fortyFiveAQ_54721 : Nat.Prime 54721 := by norm_num
private theorem prime_fortyFiveAQ_55051 : Nat.Prime 55051 := by norm_num
private theorem prime_fortyFiveAQ_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_fortyFiveAQ_60607 : Nat.Prime 60607 := by norm_num
private theorem prime_fortyFiveAQ_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_fortyFiveAQ_61261 : Nat.Prime 61261 := by norm_num
private theorem prime_fortyFiveAQ_61553 : Nat.Prime 61553 := by norm_num
private theorem prime_fortyFiveAQ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyFiveAQ_64793 : Nat.Prime 64793 := by norm_num
private theorem prime_fortyFiveAQ_66109 : Nat.Prime 66109 := by norm_num
private theorem prime_fortyFiveAQ_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_fortyFiveAQ_75389 : Nat.Prime 75389 := by norm_num
private theorem prime_fortyFiveAQ_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_fortyFiveAQ_76649 : Nat.Prime 76649 := by norm_num
private theorem prime_fortyFiveAQ_77351 : Nat.Prime 77351 := by norm_num
private theorem prime_fortyFiveAQ_77551 : Nat.Prime 77551 := by norm_num
private theorem prime_fortyFiveAQ_78901 : Nat.Prime 78901 := by norm_num
private theorem prime_fortyFiveAQ_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fortyFiveAQ_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_fortyFiveAQ_86843 : Nat.Prime 86843 := by norm_num
private theorem prime_fortyFiveAQ_91813 : Nat.Prime 91813 := by norm_num
private theorem prime_fortyFiveAQ_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fortyFiveAQ_94151 : Nat.Prime 94151 := by norm_num
private theorem prime_fortyFiveAQ_95083 : Nat.Prime 95083 := by norm_num
private theorem prime_fortyFiveAQ_96293 : Nat.Prime 96293 := by norm_num
private theorem prime_fortyFiveAQ_99367 : Nat.Prime 99367 := by norm_num
private theorem prime_fortyFiveAQ_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_fortyFiveAQ_105107 : Nat.Prime 105107 := by norm_num
private theorem prime_fortyFiveAQ_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_fortyFiveAQ_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fortyFiveAQ_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_fortyFiveAQ_123581 : Nat.Prime 123581 := by norm_num
private theorem prime_fortyFiveAQ_129209 : Nat.Prime 129209 := by norm_num
private theorem prime_fortyFiveAQ_131371 : Nat.Prime 131371 := by norm_num
private theorem prime_fortyFiveAQ_132383 : Nat.Prime 132383 := by norm_num
private theorem prime_fortyFiveAQ_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_fortyFiveAQ_146681 : Nat.Prime 146681 := by norm_num
private theorem prime_fortyFiveAQ_160709 : Nat.Prime 160709 := by norm_num
private theorem prime_fortyFiveAQ_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fortyFiveAQ_161093 : Nat.Prime 161093 := by norm_num
private theorem prime_fortyFiveAQ_161527 : Nat.Prime 161527 := by norm_num
private theorem prime_fortyFiveAQ_163927 : Nat.Prime 163927 := by norm_num
private theorem prime_fortyFiveAQ_164881 : Nat.Prime 164881 := by norm_num
private theorem prime_fortyFiveAQ_165463 : Nat.Prime 165463 := by norm_num
private theorem prime_fortyFiveAQ_171877 : Nat.Prime 171877 := by norm_num
private theorem prime_fortyFiveAQ_182107 : Nat.Prime 182107 := by norm_num
private theorem prime_fortyFiveAQ_202387 : Nat.Prime 202387 := by norm_num
private theorem prime_fortyFiveAQ_210169 : Nat.Prime 210169 := by norm_num
private theorem prime_fortyFiveAQ_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fortyFiveAQ_219491 : Nat.Prime 219491 := by norm_num
private theorem prime_fortyFiveAQ_230729 : Nat.Prime 230729 := by norm_num
private theorem prime_fortyFiveAQ_230969 : Nat.Prime 230969 := by norm_num
private theorem prime_fortyFiveAQ_240283 : Nat.Prime 240283 := by norm_num
private theorem prime_fortyFiveAQ_248243 : Nat.Prime 248243 := by norm_num
private theorem prime_fortyFiveAQ_276347 : Nat.Prime 276347 := by norm_num
private theorem prime_fortyFiveAQ_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_fortyFiveAQ_279073 : Nat.Prime 279073 := by norm_num
private theorem prime_fortyFiveAQ_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_fortyFiveAQ_297719 : Nat.Prime 297719 := by norm_num
private theorem prime_fortyFiveAQ_300929 : Nat.Prime 300929 := by norm_num
private theorem prime_fortyFiveAQ_339907 : Nat.Prime 339907 := by norm_num
private theorem prime_fortyFiveAQ_375101 : Nat.Prime 375101 := by norm_num
private theorem prime_fortyFiveAQ_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_fortyFiveAQ_401987 : Nat.Prime 401987 := by norm_num
private theorem prime_fortyFiveAQ_406247 : Nat.Prime 406247 := by norm_num
private theorem prime_fortyFiveAQ_407633 : Nat.Prime 407633 := by norm_num
private theorem prime_fortyFiveAQ_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_fortyFiveAQ_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_fortyFiveAQ_541589 : Nat.Prime 541589 := by norm_num
private theorem prime_fortyFiveAQ_551107 : Nat.Prime 551107 := by norm_num
private theorem prime_fortyFiveAQ_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_fortyFiveAQ_608459 : Nat.Prime 608459 := by norm_num
private theorem prime_fortyFiveAQ_611257 : Nat.Prime 611257 := by norm_num
private theorem prime_fortyFiveAQ_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_fortyFiveAQ_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_fortyFiveAQ_699299 : Nat.Prime 699299 := by norm_num
private theorem prime_fortyFiveAQ_732923 : Nat.Prime 732923 := by norm_num
private theorem prime_fortyFiveAQ_775937 : Nat.Prime 775937 := by norm_num
private theorem prime_fortyFiveAQ_819509 : Nat.Prime 819509 := by norm_num
private theorem prime_fortyFiveAQ_827923 : Nat.Prime 827923 := by norm_num
private theorem prime_fortyFiveAQ_854929 : Nat.Prime 854929 := by norm_num
private theorem prime_fortyFiveAQ_882883 : Nat.Prime 882883 := by norm_num
private theorem prime_fortyFiveAQ_887599 : Nat.Prime 887599 := by norm_num
private theorem prime_fortyFiveAQ_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_fortyFiveAQ_1056241 : Nat.Prime 1056241 := by norm_num
private theorem prime_fortyFiveAQ_1107763 : Nat.Prime 1107763 := by norm_num
private theorem prime_fortyFiveAQ_1191109 : Nat.Prime 1191109 := by norm_num
private theorem prime_fortyFiveAQ_1203121 : Nat.Prime 1203121 := by norm_num
private theorem prime_fortyFiveAQ_1297397 : Nat.Prime 1297397 := by norm_num
private theorem prime_fortyFiveAQ_1398911 : Nat.Prime 1398911 := by norm_num
private theorem prime_fortyFiveAQ_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_fortyFiveAQ_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fortyFiveAQ_1535377 : Nat.Prime 1535377 := by norm_num
private theorem prime_fortyFiveAQ_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_fortyFiveAQ_1589747 : Nat.Prime 1589747 := by norm_num
private theorem prime_fortyFiveAQ_1610561 : Nat.Prime 1610561 := by norm_num
private theorem prime_fortyFiveAQ_1701391 : Nat.Prime 1701391 := by norm_num
private theorem prime_fortyFiveAQ_1707161 : Nat.Prime 1707161 := by norm_num
private theorem prime_fortyFiveAQ_1776539 : Nat.Prime 1776539 := by norm_num
private theorem prime_fortyFiveAQ_1896161 : Nat.Prime 1896161 := by norm_num
private theorem prime_fortyFiveAQ_1983689 : Nat.Prime 1983689 := by norm_num
private theorem prime_fortyFiveAQ_1994227 : Nat.Prime 1994227 := by norm_num
private theorem prime_fortyFiveAQ_2044901 : Nat.Prime 2044901 := by norm_num
private theorem prime_fortyFiveAQ_2179291 : Nat.Prime 2179291 := by norm_num
private theorem prime_fortyFiveAQ_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_fortyFiveAQ_2231587 : Nat.Prime 2231587 := by norm_num
private theorem prime_fortyFiveAQ_2293631 : Nat.Prime 2293631 := by norm_num
private theorem prime_fortyFiveAQ_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_fortyFiveAQ_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_fortyFiveAQ_2413063 : Nat.Prime 2413063 := by norm_num
private theorem prime_fortyFiveAQ_2497849 : Nat.Prime 2497849 := by norm_num
private theorem prime_fortyFiveAQ_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_fortyFiveAQ_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_fortyFiveAQ_2832133 : Nat.Prime 2832133 := by norm_num
private theorem prime_fortyFiveAQ_3207473 : Nat.Prime 3207473 := by norm_num
private theorem prime_fortyFiveAQ_3324457 : Nat.Prime 3324457 := by norm_num
private theorem prime_fortyFiveAQ_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_fortyFiveAQ_3448607 : Nat.Prime 3448607 := by norm_num
private theorem prime_fortyFiveAQ_3450737 : Nat.Prime 3450737 := by norm_num
private theorem prime_fortyFiveAQ_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_fortyFiveAQ_3636779 : Nat.Prime 3636779 := by norm_num
private theorem prime_fortyFiveAQ_3848951 : Nat.Prime 3848951 := by norm_num
private theorem prime_fortyFiveAQ_4143101 : Nat.Prime 4143101 := by norm_num
private theorem prime_fortyFiveAQ_4183909 : Nat.Prime 4183909 := by norm_num
private theorem prime_fortyFiveAQ_4567973 : Nat.Prime 4567973 := by norm_num
private theorem prime_fortyFiveAQ_4644463 : Nat.Prime 4644463 := by norm_num
private theorem prime_fortyFiveAQ_4952377 : Nat.Prime 4952377 := by norm_num
private theorem prime_fortyFiveAQ_4979131 : Nat.Prime 4979131 := by norm_num
private theorem prime_fortyFiveAQ_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_fortyFiveAQ_5145949 : Nat.Prime 5145949 := by norm_num
private theorem prime_fortyFiveAQ_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_fortyFiveAQ_5283683 : Nat.Prime 5283683 := by norm_num
private theorem prime_fortyFiveAQ_5301391 : Nat.Prime 5301391 := by norm_num
private theorem prime_fortyFiveAQ_6065239 : Nat.Prime 6065239 := by norm_num
private theorem prime_fortyFiveAQ_6759017 : Nat.Prime 6759017 := by norm_num
private theorem prime_fortyFiveAQ_7049167 : Nat.Prime 7049167 := by norm_num
private theorem prime_fortyFiveAQ_7100183 : Nat.Prime 7100183 := by norm_num
private theorem prime_fortyFiveAQ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyFiveAQ_7372283 : Nat.Prime 7372283 := by norm_num
private theorem prime_fortyFiveAQ_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_fortyFiveAQ_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_fortyFiveAQ_7910317 : Nat.Prime 7910317 := by norm_num
private theorem prime_fortyFiveAQ_8200217 : Nat.Prime 8200217 := by norm_num
private theorem prime_fortyFiveAQ_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fortyFiveAQ_8810759 : Nat.Prime 8810759 := by norm_num
private theorem prime_fortyFiveAQ_8870999 : Nat.Prime 8870999 := by norm_num
private theorem prime_fortyFiveAQ_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_fortyFiveAQ_9301769 : Nat.Prime 9301769 := by norm_num
private theorem prime_fortyFiveAQ_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fortyFiveAQ_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_fortyFiveAQ_11484449 : Nat.Prime 11484449 := by norm_num
private theorem prime_fortyFiveAQ_11527561 : Nat.Prime 11527561 := by norm_num
private theorem prime_fortyFiveAQ_11909399 : Nat.Prime 11909399 := by norm_num
private theorem prime_fortyFiveAQ_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_fortyFiveAQ_12864823 : Nat.Prime 12864823 := by norm_num
private theorem prime_fortyFiveAQ_12942901 : Nat.Prime 12942901 := by norm_num
private theorem prime_fortyFiveAQ_13245811 : Nat.Prime 13245811 := by norm_num
private theorem prime_fortyFiveAQ_13263763 : Nat.Prime 13263763 := by norm_num
private theorem prime_fortyFiveAQ_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_fortyFiveAQ_14652643 : Nat.Prime 14652643 := by norm_num
private theorem prime_fortyFiveAQ_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fortyFiveAQ_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_fortyFiveAQ_16568887 : Nat.Prime 16568887 := by norm_num
private theorem prime_fortyFiveAQ_17069027 : Nat.Prime 17069027 := by norm_num
private theorem prime_fortyFiveAQ_17732083 : Nat.Prime 17732083 := by norm_num
private theorem prime_fortyFiveAQ_17834879 : Nat.Prime 17834879 := by norm_num
private theorem prime_fortyFiveAQ_19031057 : Nat.Prime 19031057 := by norm_num
private theorem prime_fortyFiveAQ_20025517 : Nat.Prime 20025517 := by norm_num
private theorem prime_fortyFiveAQ_20575691 : Nat.Prime 20575691 := by norm_num
private theorem prime_fortyFiveAQ_21177731 : Nat.Prime 21177731 := by norm_num
private theorem prime_fortyFiveAQ_21675737 : Nat.Prime 21675737 := by norm_num
private theorem prime_fortyFiveAQ_22447727 : Nat.Prime 22447727 := by norm_num
private theorem prime_fortyFiveAQ_23218313 : Nat.Prime 23218313 := by norm_num
private theorem prime_fortyFiveAQ_26126021 : Nat.Prime 26126021 := by norm_num
private theorem prime_fortyFiveAQ_26242127 : Nat.Prime 26242127 := by norm_num
private theorem prime_fortyFiveAQ_27448273 : Nat.Prime 27448273 := by norm_num
private theorem prime_fortyFiveAQ_27481037 : Nat.Prime 27481037 := by norm_num
private theorem prime_fortyFiveAQ_28680341 : Nat.Prime 28680341 := by norm_num

private theorem prime_fortyFiveAQ_33351053 : Nat.Prime 33351053 := by
  apply lucas_primality 33351053 (2 : ZMod 33351053)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod) = 33351053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_1191109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33351053) ^ 16675526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 4764436 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 28 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_34337111 : Nat.Prime 34337111 := by
  apply lucas_primality 34337111 (7 : ZMod 34337111)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (37, 1), (53, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (37, 1), (53, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 34337111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34337111) ^ 17168555 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 34337111) ^ 6867422 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 34337111) ^ 2019830 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 34337111) ^ 928030 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 34337111) ^ 647870 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 34337111) ^ 333370 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_34949077 : Nat.Prime 34949077 := by
  apply lucas_primality 34949077 (2 : ZMod 34949077)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (67, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (67, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod) = 34949077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_67
      · exact prime_fortyFiveAQ_2557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34949077) ^ 17474538 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34949077) ^ 11649692 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34949077) ^ 2055828 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34949077) ^ 521628 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34949077) ^ 13668 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_36944819 : Nat.Prime 36944819 := by
  apply lucas_primality 36944819 (2 : ZMod 36944819)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (76649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (76649, 1)] : List FactorBlock).map factorBlockValue).prod) = 36944819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_241
      · exact prime_fortyFiveAQ_76649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36944819) ^ 18472409 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36944819) ^ 153298 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36944819) ^ 482 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_37663943 : Nat.Prime 37663943 := by
  apply lucas_primality 37663943 (5 : ZMod 37663943)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1107763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1107763, 1)] : List FactorBlock).map factorBlockValue).prod) = 37663943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_1107763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37663943) ^ 18831971 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 37663943) ^ 2215526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 37663943) ^ 34 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_38559853 : Nat.Prime 38559853 := by
  apply lucas_primality 38559853 (5 : ZMod 38559853)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) = 38559853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_787
      · exact prime_fortyFiveAQ_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38559853) ^ 19279926 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 12853284 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 48996 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 28332 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_39364363 : Nat.Prime 39364363 := by
  apply lucas_primality 39364363 (3 : ZMod 39364363)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) = 39364363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_95083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39364363) ^ 19682181 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39364363) ^ 13121454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39364363) ^ 1711494 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39364363) ^ 414 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_39702781 : Nat.Prime 39702781 := by
  apply lucas_primality 39702781 (2 : ZMod 39702781)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (19, 2), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (19, 2), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 39702781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39702781) ^ 19851390 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39702781) ^ 13234260 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39702781) ^ 7940556 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39702781) ^ 3054060 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39702781) ^ 2089620 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39702781) ^ 844740 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_42466681 : Nat.Prime 42466681 := by
  apply lucas_primality 42466681 (7 : ZMod 42466681)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 42466681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42466681) ^ 21233340 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 14155560 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 8493336 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 2498040 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 165240 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_45274987 : Nat.Prime 45274987 := by
  apply lucas_primality 45274987 (2 : ZMod 45274987)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod) = 45274987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_132383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45274987) ^ 22637493 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 15091662 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 2382894 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 342 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_49201177 : Nat.Prime 49201177 := by
  apply lucas_primality 49201177 (5 : ZMod 49201177)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (269, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (269, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) = 49201177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_269
      · exact prime_fortyFiveAQ_7621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49201177) ^ 24600588 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49201177) ^ 16400392 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49201177) ^ 182904 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49201177) ^ 6456 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_49201303 : Nat.Prime 49201303 := by
  apply lucas_primality 49201303 (29 : ZMod 49201303)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8200217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8200217, 1)] : List FactorBlock).map factorBlockValue).prod) = 49201303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_8200217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 49201303) ^ 24600651 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (29 : ZMod 49201303) ^ 16400434 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (29 : ZMod 49201303) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_53055053 : Nat.Prime 53055053 := by
  apply lucas_primality 53055053 (2 : ZMod 53055053)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13263763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13263763, 1)] : List FactorBlock).map factorBlockValue).prod) = 53055053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13263763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 53055053) ^ 26527526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 53055053) ^ 4 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_56120221 : Nat.Prime 56120221 := by
  apply lucas_primality 56120221 (7 : ZMod 56120221)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (29, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (29, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) = 56120221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56120221) ^ 28060110 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 56120221) ^ 18706740 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 56120221) ^ 11224044 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 56120221) ^ 4316940 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 56120221) ^ 1935180 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 56120221) ^ 67860 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_60017669 : Nat.Prime 60017669 := by
  apply lucas_primality 60017669 (2 : ZMod 60017669)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (99367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (99367, 1)] : List FactorBlock).map factorBlockValue).prod) = 60017669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_151
      · exact prime_fortyFiveAQ_99367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60017669) ^ 30008834 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60017669) ^ 397468 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60017669) ^ 604 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_60652391 : Nat.Prime 60652391 := by
  apply lucas_primality 60652391 (7 : ZMod 60652391)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6065239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6065239, 1)] : List FactorBlock).map factorBlockValue).prod) = 60652391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_6065239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 60652391) ^ 30326195 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 60652391) ^ 12130478 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 60652391) ^ 10 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_62386199 : Nat.Prime 62386199 := by
  apply lucas_primality 62386199 (7 : ZMod 62386199)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 2), (4637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 2), (4637, 1)] : List FactorBlock).map factorBlockValue).prod) = 62386199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_4637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 62386199) ^ 31193099 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 62386199) ^ 8912314 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 62386199) ^ 2012458 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 62386199) ^ 13454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_67674419 : Nat.Prime 67674419 := by
  apply lucas_primality 67674419 (2 : ZMod 67674419)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (210169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (210169, 1)] : List FactorBlock).map factorBlockValue).prod) = 67674419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_210169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67674419) ^ 33837209 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67674419) ^ 9667774 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67674419) ^ 2942366 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67674419) ^ 322 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_68674223 : Nat.Prime 68674223 := by
  apply lucas_primality 68674223 (5 : ZMod 68674223)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34337111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34337111, 1)] : List FactorBlock).map factorBlockValue).prod) = 68674223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_34337111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 68674223) ^ 34337111 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 68674223) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_72878753 : Nat.Prime 72878753 := by
  apply lucas_primality 72878753 (3 : ZMod 72878753)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (61553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (61553, 1)] : List FactorBlock).map factorBlockValue).prod) = 72878753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_61553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72878753) ^ 36439376 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 72878753) ^ 1969696 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 72878753) ^ 1184 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_73693313 : Nat.Prime 73693313 := by
  apply lucas_primality 73693313 (3 : ZMod 73693313)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (11, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (11, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) = 73693313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_7477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73693313) ^ 36846656 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73693313) ^ 10527616 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73693313) ^ 6699392 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73693313) ^ 9856 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_81108667 : Nat.Prime 81108667 := by
  apply lucas_primality 81108667 (3 : ZMod 81108667)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (401, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (401, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 81108667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_401
      · exact prime_fortyFiveAQ_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81108667) ^ 40554333 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 81108667) ^ 27036222 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 81108667) ^ 4771098 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 81108667) ^ 202266 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 81108667) ^ 122706 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_82621199 : Nat.Prime 82621199 := by
  apply lucas_primality 82621199 (11 : ZMod 82621199)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 82621199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_269
      · exact prime_fortyFiveAQ_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 82621199) ^ 41310599 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 7511018 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 3592226 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 307142 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 136114 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_96784273 : Nat.Prime 96784273 := by
  apply lucas_primality 96784273 (5 : ZMod 96784273)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 2), (41, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 2), (41, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 96784273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 96784273) ^ 48392136 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96784273) ^ 32261424 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96784273) ^ 7444944 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96784273) ^ 2360592 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96784273) ^ 997776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_120035339 : Nat.Prime 120035339 := by
  apply lucas_primality 120035339 (2 : ZMod 120035339)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60017669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60017669, 1)] : List FactorBlock).map factorBlockValue).prod) = 120035339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_60017669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 120035339) ^ 60017669 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 120035339) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_151206773 : Nat.Prime 151206773 := by
  apply lucas_primality 151206773 (2 : ZMod 151206773)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (641, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (641, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 151206773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_641
      · exact prime_fortyFiveAQ_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151206773) ^ 75603386 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 151206773) ^ 8894516 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 151206773) ^ 235892 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 151206773) ^ 43588 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_155314813 : Nat.Prime 155314813 := by
  apply lucas_primality 155314813 (2 : ZMod 155314813)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12942901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12942901, 1)] : List FactorBlock).map factorBlockValue).prod) = 155314813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_12942901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 155314813) ^ 77657406 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 155314813) ^ 51771604 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 155314813) ^ 12 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_196191613 : Nat.Prime 196191613 := by
  apply lucas_primality 196191613 (2 : ZMod 196191613)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 1), (37, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 1), (37, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 196191613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 196191613) ^ 98095806 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 196191613) ^ 65397204 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 196191613) ^ 6765228 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 196191613) ^ 5302476 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 196191613) ^ 115884 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_228550559 : Nat.Prime 228550559 := by
  apply lucas_primality 228550559 (37 : ZMod 228550559)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod) = 228550559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_211
      · exact prime_fortyFiveAQ_541589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 228550559) ^ 114275279 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 1083178 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 422 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_243409363 : Nat.Prime 243409363 := by
  apply lucas_primality 243409363 (2 : ZMod 243409363)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (827923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (827923, 1)] : List FactorBlock).map factorBlockValue).prod) = 243409363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_827923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243409363) ^ 121704681 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243409363) ^ 81136454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243409363) ^ 34772766 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243409363) ^ 294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_245529233 : Nat.Prime 245529233 := by
  apply lucas_primality 245529233 (3 : ZMod 245529233)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 1), (23, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 1), (23, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) = 245529233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_3019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 245529233) ^ 122764616 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 245529233) ^ 18886864 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 245529233) ^ 14442896 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 245529233) ^ 10675184 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 245529233) ^ 81328 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_260861261 : Nat.Prime 260861261 := by
  apply lucas_primality 260861261 (2 : ZMod 260861261)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (17, 1), (19, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (17, 1), (19, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) = 260861261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_3671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 260861261) ^ 130430630 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 260861261) ^ 52172252 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 260861261) ^ 23714660 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 260861261) ^ 15344780 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 260861261) ^ 13729540 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 260861261) ^ 71060 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_275672333 : Nat.Prime 275672333 := by
  apply lucas_primality 275672333 (3 : ZMod 275672333)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod) = 275672333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_5301391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 275672333) ^ 137836166 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 21205564 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 52 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_285318883 : Nat.Prime 285318883 := by
  apply lucas_primality 285318883 (2 : ZMod 285318883)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod) = 285318883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5283683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 285318883) ^ 142659441 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 95106294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 54 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod) = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod) = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5437
      · exact prime_fortyFiveAQ_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_325800521 : Nat.Prime 325800521 := by
  apply lucas_primality 325800521 (3 : ZMod 325800521)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 325800521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_89
      · exact prime_fortyFiveAQ_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325800521) ^ 162900260 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 65160104 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 14165240 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 3660680 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 1883240 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_341996947 : Nat.Prime 341996947 := by
  apply lucas_primality 341996947 (2 : ZMod 341996947)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (182107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (182107, 1)] : List FactorBlock).map factorBlockValue).prod) = 341996947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_313
      · exact prime_fortyFiveAQ_182107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 341996947) ^ 170998473 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 341996947) ^ 113998982 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 341996947) ^ 1092642 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 341996947) ^ 1878 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_362583961 : Nat.Prime 362583961 := by
  apply lucas_primality 362583961 (14 : ZMod 362583961)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod) = 362583961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_131371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 362583961) ^ 181291980 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 120861320 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 72516792 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 15764520 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 2760 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_380845967 : Nat.Prime 380845967 := by
  apply lucas_primality 380845967 (5 : ZMod 380845967)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (4644463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (4644463, 1)] : List FactorBlock).map factorBlockValue).prod) = 380845967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_4644463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 380845967) ^ 190422983 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 380845967) ^ 9288926 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 380845967) ^ 82 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_439346137 : Nat.Prime 439346137 := by
  apply lucas_primality 439346137 (5 : ZMod 439346137)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 2), (43, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 2), (43, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 439346137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 439346137) ^ 219673068 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 439346137) ^ 146448712 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 439346137) ^ 14172456 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 439346137) ^ 10217352 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 439346137) ^ 991752 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_454055887 : Nat.Prime 454055887 := by
  apply lucas_primality 454055887 (3 : ZMod 454055887)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1409, 1), (17903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1409, 1), (17903, 1)] : List FactorBlock).map factorBlockValue).prod) = 454055887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_1409
      · exact prime_fortyFiveAQ_17903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454055887) ^ 227027943 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454055887) ^ 151351962 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454055887) ^ 322254 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 454055887) ^ 25362 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_473251901 : Nat.Prime 473251901 := by
  apply lucas_primality 473251901 (3 : ZMod 473251901)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (211, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (211, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) = 473251901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_211
      · exact prime_fortyFiveAQ_2039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 473251901) ^ 236625950 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 473251901) ^ 94650380 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 473251901) ^ 43022900 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 473251901) ^ 2242900 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 473251901) ^ 232100 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_541395353 : Nat.Prime 541395353 := by
  apply lucas_primality 541395353 (3 : ZMod 541395353)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67674419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67674419, 1)] : List FactorBlock).map factorBlockValue).prod) = 541395353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_67674419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 541395353) ^ 270697676 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 541395353) ^ 8 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_722420821 : Nat.Prime 722420821 := by
  apply lucas_primality 722420821 (2 : ZMod 722420821)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 2), (41, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 2), (41, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 722420821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 722420821) ^ 361210410 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 722420821) ^ 240806940 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 722420821) ^ 144484164 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 722420821) ^ 65674620 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 722420821) ^ 17620020 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 722420821) ^ 892980 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_912772537 : Nat.Prime 912772537 := by
  apply lucas_primality 912772537 (7 : ZMod 912772537)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 912772537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 912772537) ^ 456386268 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 304257512 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 70213272 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 24669528 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 427128 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_973430641 : Nat.Prime 973430641 := by
  apply lucas_primality 973430641 (11 : ZMod 973430641)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (13, 1), (83, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (13, 1), (83, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 973430641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_83
      · exact prime_fortyFiveAQ_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 973430641) ^ 486715320 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 324476880 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 194686128 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 139061520 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 74879280 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 11728080 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 973430641) ^ 5438160 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_973637453 : Nat.Prime 973637453 := by
  apply lucas_primality 973637453 (2 : ZMod 973637453)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (243409363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (243409363, 1)] : List FactorBlock).map factorBlockValue).prod) = 973637453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_243409363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 973637453) ^ 486818726 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 973637453) ^ 4 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_979262519 : Nat.Prime 979262519 := by
  apply lucas_primality 979262519 (7 : ZMod 979262519)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37663943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37663943, 1)] : List FactorBlock).map factorBlockValue).prod) = 979262519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_37663943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 979262519) ^ 489631259 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 979262519) ^ 75327886 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 979262519) ^ 26 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1000462471 : Nat.Prime 1000462471 := by
  apply lucas_primality 1000462471 (6 : ZMod 1000462471)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1789, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1789, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1000462471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_1789
      · exact prime_fortyFiveAQ_2663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1000462471) ^ 500231235 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1000462471) ^ 333487490 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1000462471) ^ 200092494 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1000462471) ^ 142923210 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1000462471) ^ 559230 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1000462471) ^ 375690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1032896747 : Nat.Prime 1032896747 := by
  apply lucas_primality 1032896747 (2 : ZMod 1032896747)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1032896747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_571
      · exact prime_fortyFiveAQ_129209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1032896747) ^ 516448373 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 147556678 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 1808926 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 7994 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1113694831 : Nat.Prime 1113694831 := by
  apply lucas_primality 1113694831 (3 : ZMod 1113694831)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (53, 1), (83, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (53, 1), (83, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113694831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_83
      · exact prime_fortyFiveAQ_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1113694831) ^ 556847415 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 371231610 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 222738966 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 38403270 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 21013110 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 13418010 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1113694831) ^ 11481390 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1177149679 : Nat.Prime 1177149679 := by
  apply lucas_primality 1177149679 (15 : ZMod 1177149679)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (196191613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (196191613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1177149679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_196191613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 1177149679) ^ 588574839 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (15 : ZMod 1177149679) ^ 392383226 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (15 : ZMod 1177149679) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_113
      · exact prime_fortyFiveAQ_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_79
      · exact prime_fortyFiveAQ_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1779481213 : Nat.Prime 1779481213 := by
  apply lucas_primality 1779481213 (2 : ZMod 1779481213)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1779481213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_3448607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1779481213) ^ 889740606 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 593160404 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 41383284 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 516 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1831691527 : Nat.Prime 1831691527 := by
  apply lucas_primality 1831691527 (5 : ZMod 1831691527)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1831691527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_1896161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1831691527) ^ 915845763 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 610563842 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 261670218 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 79638762 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 966 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1870427107 : Nat.Prime 1870427107 := by
  apply lucas_primality 1870427107 (2 : ZMod 1870427107)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (439, 1), (78901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (439, 1), (78901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1870427107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_439
      · exact prime_fortyFiveAQ_78901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1870427107) ^ 935213553 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870427107) ^ 623475702 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870427107) ^ 4260654 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870427107) ^ 23706 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_89
      · exact prime_fortyFiveAQ_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2237066599 : Nat.Prime 2237066599 := by
  apply lucas_primality 2237066599 (3 : ZMod 2237066599)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (28680341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (28680341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2237066599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_28680341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2237066599) ^ 1118533299 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2237066599) ^ 745688866 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2237066599) ^ 172082046 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2237066599) ^ 78 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2347844113 : Nat.Prime 2347844113 := by
  apply lucas_primality 2347844113 (5 : ZMod 2347844113)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (59, 1), (276347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (59, 1), (276347, 1)] : List FactorBlock).map factorBlockValue).prod) = 2347844113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_276347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2347844113) ^ 1173922056 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2347844113) ^ 782614704 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2347844113) ^ 39793968 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2347844113) ^ 8496 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_61
      · exact prime_fortyFiveAQ_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_239
      · exact prime_fortyFiveAQ_283
      · exact prime_fortyFiveAQ_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2553277297 : Nat.Prime 2553277297 := by
  apply lucas_primality 2553277297 (10 : ZMod 2553277297)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (1297397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (1297397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2553277297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_1297397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2553277297) ^ 1276638648 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2553277297) ^ 851092432 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2553277297) ^ 62275056 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2553277297) ^ 1968 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2610980759 : Nat.Prime 2610980759 := by
  apply lucas_primality 2610980759 (7 : ZMod 2610980759)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (743, 1), (7541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (743, 1), (7541, 1)] : List FactorBlock).map factorBlockValue).prod) = 2610980759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_233
      · exact prime_fortyFiveAQ_743
      · exact prime_fortyFiveAQ_7541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2610980759) ^ 1305490379 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2610980759) ^ 11205926 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2610980759) ^ 3514106 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2610980759) ^ 346238 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2716160977 : Nat.Prime 2716160977 := by
  apply lucas_primality 2716160977 (5 : ZMod 2716160977)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (608459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (608459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2716160977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_608459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2716160977) ^ 1358080488 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2716160977) ^ 905386992 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2716160977) ^ 87618096 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2716160977) ^ 4464 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2832143261 : Nat.Prime 2832143261 := by
  apply lucas_primality 2832143261 (2 : ZMod 2832143261)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod) = 2832143261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_4567973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2832143261) ^ 1416071630 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 566428652 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 91359460 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 620 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3343934329 : Nat.Prime 3343934329 := by
  apply lucas_primality 3343934329 (11 : ZMod 3343934329)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1873, 1), (10627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1873, 1), (10627, 1)] : List FactorBlock).map factorBlockValue).prod) = 3343934329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_1873
      · exact prime_fortyFiveAQ_10627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3343934329) ^ 1671967164 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3343934329) ^ 1114644776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3343934329) ^ 477704904 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3343934329) ^ 1785336 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3343934329) ^ 314664 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3771531487 : Nat.Prime 3771531487 := by
  apply lucas_primality 3771531487 (3 : ZMod 3771531487)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3771531487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_6759017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3771531487) ^ 1885765743 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 1257177162 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 121662306 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 558 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4066124353 : Nat.Prime 4066124353 := by
  apply lucas_primality 4066124353 (5 : ZMod 4066124353)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (21177731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (21177731, 1)] : List FactorBlock).map factorBlockValue).prod) = 4066124353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_21177731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4066124353) ^ 2033062176 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4066124353) ^ 1355374784 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4066124353) ^ 192 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod) = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_5142576451 : Nat.Prime 5142576451 := by
  apply lucas_primality 5142576451 (2 : ZMod 5142576451)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (1031, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (1031, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) = 5142576451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_1031
      · exact prime_fortyFiveAQ_3023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5142576451) ^ 2571288225 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5142576451) ^ 1714192150 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5142576451) ^ 1028515290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5142576451) ^ 467506950 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5142576451) ^ 4987950 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5142576451) ^ 1701150 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_5280703643 : Nat.Prime 5280703643 := by
  apply lucas_primality 5280703643 (2 : ZMod 5280703643)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (155314813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (155314813, 1)] : List FactorBlock).map factorBlockValue).prod) = 5280703643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_155314813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5280703643) ^ 2640351821 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5280703643) ^ 310629626 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5280703643) ^ 34 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_89
      · exact prime_fortyFiveAQ_223
      · exact prime_fortyFiveAQ_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod) = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_1483
      · exact prime_fortyFiveAQ_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_6996360289 : Nat.Prime 6996360289 := by
  apply lucas_primality 6996360289 (22 : ZMod 6996360289)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (72878753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (72878753, 1)] : List FactorBlock).map factorBlockValue).prod) = 6996360289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_72878753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (22 : ZMod 6996360289) ^ 3498180144 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (22 : ZMod 6996360289) ^ 2332120096 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (22 : ZMod 6996360289) ^ 96 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7236045083 : Nat.Prime 7236045083 := by
  apply lucas_primality 7236045083 (2 : ZMod 7236045083)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (47, 1), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (47, 1), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) = 7236045083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_15643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7236045083) ^ 3618022541 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236045083) ^ 1033720726 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236045083) ^ 380844478 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236045083) ^ 195568786 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236045083) ^ 153958406 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236045083) ^ 462574 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7514213933 : Nat.Prime 7514213933 := by
  apply lucas_primality 7514213933 (2 : ZMod 7514213933)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod) = 7514213933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_947
      · exact prime_fortyFiveAQ_1983689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7514213933) ^ 3757106966 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 7934756 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 3788 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7712740241 : Nat.Prime 7712740241 := by
  apply lucas_primality 7712740241 (7 : ZMod 7712740241)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (3324457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (3324457, 1)] : List FactorBlock).map factorBlockValue).prod) = 7712740241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_3324457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7712740241) ^ 3856370120 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7712740241) ^ 1542548048 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7712740241) ^ 265956560 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7712740241) ^ 2320 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_73
      · exact prime_fortyFiveAQ_397
      · exact prime_fortyFiveAQ_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod) = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_11222562643 : Nat.Prime 11222562643 := by
  apply lucas_primality 11222562643 (2 : ZMod 11222562643)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1870427107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1870427107, 1)] : List FactorBlock).map factorBlockValue).prod) = 11222562643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_1870427107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11222562643) ^ 5611281321 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11222562643) ^ 3740854214 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11222562643) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_11602217353 : Nat.Prime 11602217353 := by
  apply lucas_primality 11602217353 (5 : ZMod 11602217353)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (71, 1), (701, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (71, 1), (701, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 11602217353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_71
      · exact prime_fortyFiveAQ_701
      · exact prime_fortyFiveAQ_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11602217353) ^ 5801108676 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11602217353) ^ 3867405784 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11602217353) ^ 1054747032 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11602217353) ^ 163411512 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11602217353) ^ 16550952 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11602217353) ^ 13139544 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_12488895919 : Nat.Prime 12488895919 := by
  apply lucas_primality 12488895919 (6 : ZMod 12488895919)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (73, 1), (161093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (73, 1), (161093, 1)] : List FactorBlock).map factorBlockValue).prod) = 12488895919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_73
      · exact prime_fortyFiveAQ_161093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12488895919) ^ 6244447959 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 12488895919) ^ 4162965306 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 12488895919) ^ 211676202 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 12488895919) ^ 171080766 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 12488895919) ^ 77526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_349
      · exact prime_fortyFiveAQ_619
      · exact prime_fortyFiveAQ_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_15148257011 : Nat.Prime 15148257011 := by
  apply lucas_primality 15148257011 (2 : ZMod 15148257011)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (53, 1), (73, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (53, 1), (73, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 15148257011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_73
      · exact prime_fortyFiveAQ_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15148257011) ^ 7574128505 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 3029651402 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 658619870 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 522353690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 285816170 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 207510370 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15148257011) ^ 25806230 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_18395368441 : Nat.Prime 18395368441 := by
  apply lucas_primality 18395368441 (13 : ZMod 18395368441)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (37, 1), (4143101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (37, 1), (4143101, 1)] : List FactorBlock).map factorBlockValue).prod) = 18395368441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_4143101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18395368441) ^ 9197684220 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18395368441) ^ 6131789480 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18395368441) ^ 3679073688 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18395368441) ^ 497172120 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18395368441) ^ 4440 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_19119465479 : Nat.Prime 19119465479 := by
  apply lucas_primality 19119465479 (7 : ZMod 19119465479)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1693, 1), (77351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1693, 1), (77351, 1)] : List FactorBlock).map factorBlockValue).prod) = 19119465479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_73
      · exact prime_fortyFiveAQ_1693
      · exact prime_fortyFiveAQ_77351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19119465479) ^ 9559732739 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19119465479) ^ 261910486 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19119465479) ^ 11293246 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19119465479) ^ 247178 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_127
      · exact prime_fortyFiveAQ_193
      · exact prime_fortyFiveAQ_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_23588884843 : Nat.Prime 23588884843 := by
  apply lucas_primality 23588884843 (2 : ZMod 23588884843)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2213, 1), (1776539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2213, 1), (1776539, 1)] : List FactorBlock).map factorBlockValue).prod) = 23588884843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_2213
      · exact prime_fortyFiveAQ_1776539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23588884843) ^ 11794442421 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23588884843) ^ 7862961614 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23588884843) ^ 10659234 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23588884843) ^ 13278 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_71
      · exact prime_fortyFiveAQ_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_29811610063 : Nat.Prime 29811610063 := by
  apply lucas_primality 29811610063 (3 : ZMod 29811610063)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod) = 29811610063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_42466681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29811610063) ^ 14905805031 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 9937203354 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 2293200774 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 702 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_71
      · exact prime_fortyFiveAQ_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_37745866471 : Nat.Prime 37745866471 := by
  apply lucas_primality 37745866471 (3 : ZMod 37745866471)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (96784273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (96784273, 1)] : List FactorBlock).map factorBlockValue).prod) = 37745866471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_96784273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37745866471) ^ 18872933235 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37745866471) ^ 12581955490 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37745866471) ^ 7549173294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37745866471) ^ 2903528190 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37745866471) ^ 390 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_39484221163 : Nat.Prime 39484221163 := by
  apply lucas_primality 39484221163 (3 : ZMod 39484221163)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (2767, 1), (8117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (2767, 1), (8117, 1)] : List FactorBlock).map factorBlockValue).prod) = 39484221163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_293
      · exact prime_fortyFiveAQ_2767
      · exact prime_fortyFiveAQ_8117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39484221163) ^ 19742110581 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39484221163) ^ 13161407054 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39484221163) ^ 134758434 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39484221163) ^ 14269686 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 39484221163) ^ 4864386 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_42654616243 : Nat.Prime 42654616243 := by
  apply lucas_primality 42654616243 (2 : ZMod 42654616243)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (27448273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (27448273, 1)] : List FactorBlock).map factorBlockValue).prod) = 42654616243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_27448273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42654616243) ^ 21327308121 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42654616243) ^ 14218205414 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42654616243) ^ 6093516606 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42654616243) ^ 1152827466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42654616243) ^ 1554 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_47004600913 : Nat.Prime 47004600913 := by
  apply lucas_primality 47004600913 (10 : ZMod 47004600913)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (979262519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (979262519, 1)] : List FactorBlock).map factorBlockValue).prod) = 47004600913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_979262519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 47004600913) ^ 23502300456 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 47004600913) ^ 15668200304 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 47004600913) ^ 48 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod) = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_54011924819 : Nat.Prime 54011924819 := by
  apply lucas_primality 54011924819 (2 : ZMod 54011924819)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1523, 1), (17732083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1523, 1), (17732083, 1)] : List FactorBlock).map factorBlockValue).prod) = 54011924819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_1523
      · exact prime_fortyFiveAQ_17732083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54011924819) ^ 27005962409 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 54011924819) ^ 35464166 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 54011924819) ^ 3046 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_61710917413 : Nat.Prime 61710917413 := by
  apply lucas_primality 61710917413 (5 : ZMod 61710917413)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5142576451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5142576451, 1)] : List FactorBlock).map factorBlockValue).prod) = 61710917413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5142576451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 61710917413) ^ 30855458706 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 61710917413) ^ 20570305804 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 61710917413) ^ 12 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_66352936957 : Nat.Prime 66352936957 := by
  apply lucas_primality 66352936957 (5 : ZMod 66352936957)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (199, 1), (337, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (199, 1), (337, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 66352936957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_199
      · exact prime_fortyFiveAQ_337
      · exact prime_fortyFiveAQ_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 66352936957) ^ 33176468478 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66352936957) ^ 22117645652 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66352936957) ^ 1618364316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66352936957) ^ 333431844 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66352936957) ^ 196892988 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66352936957) ^ 32994996 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_66917996099 : Nat.Prime 66917996099 := by
  apply lucas_primality 66917996099 (2 : ZMod 66917996099)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod) = 66917996099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_173
      · exact prime_fortyFiveAQ_13901
      · exact prime_fortyFiveAQ_13913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66917996099) ^ 33458998049 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 386809226 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4813898 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4809746 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_67377094921 : Nat.Prime 67377094921 := by
  apply lucas_primality 67377094921 (7 : ZMod 67377094921)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (62386199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (62386199, 1)] : List FactorBlock).map factorBlockValue).prod) = 67377094921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_62386199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 67377094921) ^ 33688547460 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67377094921) ^ 22459031640 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67377094921) ^ 13475418984 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67377094921) ^ 1080 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_89454735767 : Nat.Prime 89454735767 := by
  apply lucas_primality 89454735767 (5 : ZMod 89454735767)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4066124353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4066124353, 1)] : List FactorBlock).map factorBlockValue).prod) = 89454735767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_4066124353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 89454735767) ^ 44727367883 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 89454735767) ^ 8132248706 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 89454735767) ^ 22 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_90160767029 : Nat.Prime 90160767029 := by
  apply lucas_primality 90160767029 (2 : ZMod 90160767029)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod) = 90160767029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_79
      · exact prime_fortyFiveAQ_285318883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90160767029) ^ 45080383514 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 1141275532 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_92349473219 : Nat.Prime 92349473219 := by
  apply lucas_primality 92349473219 (2 : ZMod 92349473219)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2716160977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2716160977, 1)] : List FactorBlock).map factorBlockValue).prod) = 92349473219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_2716160977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92349473219) ^ 46174736609 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 92349473219) ^ 5432321954 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 92349473219) ^ 34 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_93582657823 : Nat.Prime 93582657823 := by
  apply lucas_primality 93582657823 (3 : ZMod 93582657823)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod) = 93582657823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_20101
      · exact prime_fortyFiveAQ_775937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 93582657823) ^ 46791328911 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 31194219274 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 4655622 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 120606 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_97368824257 : Nat.Prime 97368824257 := by
  apply lucas_primality 97368824257 (5 : ZMod 97368824257)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod) = 97368824257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_1589747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97368824257) ^ 48684412128 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 32456274752 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 8851711296 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 3357545664 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 61248 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod) = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_167
      · exact prime_fortyFiveAQ_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_104997270029 : Nat.Prime 104997270029 := by
  apply lucas_primality 104997270029 (2 : ZMod 104997270029)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (173, 1), (21675737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (173, 1), (21675737, 1)] : List FactorBlock).map factorBlockValue).prod) = 104997270029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_173
      · exact prime_fortyFiveAQ_21675737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104997270029) ^ 52498635014 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104997270029) ^ 14999610004 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104997270029) ^ 606920636 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104997270029) ^ 4844 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_107042151929 : Nat.Prime 107042151929 := by
  apply lucas_primality 107042151929 (3 : ZMod 107042151929)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod) = 107042151929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_347
      · exact prime_fortyFiveAQ_38559853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 107042151929) ^ 53521075964 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 308478824 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 2776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod) = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_146590544473 : Nat.Prime 146590544473 := by
  apply lucas_primality 146590544473 (10 : ZMod 146590544473)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2663, 1), (2293631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2663, 1), (2293631, 1)] : List FactorBlock).map factorBlockValue).prod) = 146590544473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_2663
      · exact prime_fortyFiveAQ_2293631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 146590544473) ^ 73295272236 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 146590544473) ^ 48863514824 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 146590544473) ^ 55047144 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 146590544473) ^ 63912 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_174678882557 : Nat.Prime 174678882557 := by
  apply lucas_primality 174678882557 (2 : ZMod 174678882557)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (146681, 1), (297719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (146681, 1), (297719, 1)] : List FactorBlock).map factorBlockValue).prod) = 174678882557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_146681
      · exact prime_fortyFiveAQ_297719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 174678882557) ^ 87339441278 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 174678882557) ^ 1190876 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 174678882557) ^ 586724 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_175592882183 : Nat.Prime 175592882183 := by
  apply lucas_primality 175592882183 (10 : ZMod 175592882183)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod) = 175592882183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_2832143261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 175592882183) ^ 87796441091 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 5664286522 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 62 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_189057509411 : Nat.Prime 189057509411 := by
  apply lucas_primality 189057509411 (2 : ZMod 189057509411)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (245529233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (245529233, 1)] : List FactorBlock).map factorBlockValue).prod) = 189057509411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_245529233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 189057509411) ^ 94528754705 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 189057509411) ^ 37811501882 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 189057509411) ^ 27008215630 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 189057509411) ^ 17187046310 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 189057509411) ^ 770 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_209994540059 : Nat.Prime 209994540059 := by
  apply lucas_primality 209994540059 (2 : ZMod 209994540059)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (104997270029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (104997270029, 1)] : List FactorBlock).map factorBlockValue).prod) = 209994540059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_104997270029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 209994540059) ^ 104997270029 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 209994540059) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_237489444917 : Nat.Prime 237489444917 := by
  apply lucas_primality 237489444917 (2 : ZMod 237489444917)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (31, 1), (1433, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (31, 1), (1433, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) = 237489444917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_1433
      · exact prime_fortyFiveAQ_2711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237489444917) ^ 118744722458 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 237489444917) ^ 13969967348 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 237489444917) ^ 8189291204 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 237489444917) ^ 7660949836 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 237489444917) ^ 165728852 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 237489444917) ^ 87602156 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_237612246161 : Nat.Prime 237612246161 := by
  apply lucas_primality 237612246161 (6 : ZMod 237612246161)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1301, 1), (1499, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1301, 1), (1499, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 237612246161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_1301
      · exact prime_fortyFiveAQ_1499
      · exact prime_fortyFiveAQ_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 237612246161) ^ 118806123080 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 237612246161) ^ 47522449232 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 237612246161) ^ 182638160 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 237612246161) ^ 158513840 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 237612246161) ^ 156015920 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_257388326939 : Nat.Prime 257388326939 := by
  apply lucas_primality 257388326939 (2 : ZMod 257388326939)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8783, 1), (14652643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8783, 1), (14652643, 1)] : List FactorBlock).map factorBlockValue).prod) = 257388326939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_8783
      · exact prime_fortyFiveAQ_14652643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 257388326939) ^ 128694163469 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 257388326939) ^ 29305286 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 257388326939) ^ 17566 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_149
      · exact prime_fortyFiveAQ_1429
      · exact prime_fortyFiveAQ_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_285188866661 : Nat.Prime 285188866661 := by
  apply lucas_primality 285188866661 (7 : ZMod 285188866661)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (521, 1), (882883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (521, 1), (882883, 1)] : List FactorBlock).map factorBlockValue).prod) = 285188866661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_521
      · exact prime_fortyFiveAQ_882883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 285188866661) ^ 142594433330 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 285188866661) ^ 57037773332 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 285188866661) ^ 9199640860 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 285188866661) ^ 547387460 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 285188866661) ^ 323020 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_311531884057 : Nat.Prime 311531884057 := by
  apply lucas_primality 311531884057 (5 : ZMod 311531884057)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (1031, 1), (1398911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (1031, 1), (1398911, 1)] : List FactorBlock).map factorBlockValue).prod) = 311531884057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_1031
      · exact prime_fortyFiveAQ_1398911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 311531884057) ^ 155765942028 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 311531884057) ^ 103843961352 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 311531884057) ^ 302164776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 311531884057) ^ 222696 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_323442523387 : Nat.Prime 323442523387 := by
  apply lucas_primality 323442523387 (2 : ZMod 323442523387)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod) = 323442523387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_3719
      · exact prime_fortyFiveAQ_1610561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 323442523387) ^ 161721261693 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 107814174462 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 86970294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 200826 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_334877399159 : Nat.Prime 334877399159 := by
  apply lucas_primality 334877399159 (7 : ZMod 334877399159)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1409, 1), (854929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1409, 1), (854929, 1)] : List FactorBlock).map factorBlockValue).prod) = 334877399159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_139
      · exact prime_fortyFiveAQ_1409
      · exact prime_fortyFiveAQ_854929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 334877399159) ^ 167438699579 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 334877399159) ^ 2409189922 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 334877399159) ^ 237670262 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 334877399159) ^ 391702 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_397
      · exact prime_fortyFiveAQ_2531
      · exact prime_fortyFiveAQ_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_603362385287 : Nat.Prime 603362385287 := by
  apply lucas_primality 603362385287 (5 : ZMod 603362385287)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (271, 1), (7372283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (271, 1), (7372283, 1)] : List FactorBlock).map factorBlockValue).prod) = 603362385287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_151
      · exact prime_fortyFiveAQ_271
      · exact prime_fortyFiveAQ_7372283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 603362385287) ^ 301681192643 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 603362385287) ^ 3995777386 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 603362385287) ^ 2226429466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 603362385287) ^ 81842 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_626559317519 : Nat.Prime 626559317519 := by
  apply lucas_primality 626559317519 (7 : ZMod 626559317519)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1861, 1), (5591, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1861, 1), (5591, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) = 626559317519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_1861
      · exact prime_fortyFiveAQ_5591
      · exact prime_fortyFiveAQ_30109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 626559317519) ^ 313279658759 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 626559317519) ^ 336678838 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 626559317519) ^ 112065698 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 626559317519) ^ 20809702 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_899499665839 : Nat.Prime 899499665839 := by
  apply lucas_primality 899499665839 (11 : ZMod 899499665839)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (227, 1), (9301769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (227, 1), (9301769, 1)] : List FactorBlock).map factorBlockValue).prod) = 899499665839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_71
      · exact prime_fortyFiveAQ_227
      · exact prime_fortyFiveAQ_9301769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 899499665839) ^ 449749832919 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 899499665839) ^ 299833221946 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 899499665839) ^ 12669009378 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 899499665839) ^ 3962553594 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 899499665839) ^ 96702 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_941489444879 : Nat.Prime 941489444879 := by
  apply lucas_primality 941489444879 (7 : ZMod 941489444879)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod) = 941489444879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_257
      · exact prime_fortyFiveAQ_1831691527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 941489444879) ^ 470744722439 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 3663383054 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 514 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1032451135867 : Nat.Prime 1032451135867 := by
  apply lucas_primality 1032451135867 (2 : ZMod 1032451135867)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19119465479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19119465479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1032451135867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19119465479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1032451135867) ^ 516225567933 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032451135867) ^ 344150378622 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032451135867) ^ 54 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1069765232633 : Nat.Prime 1069765232633 := by
  apply lucas_primality 1069765232633 (3 : ZMod 1069765232633)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (4447, 1), (699299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (4447, 1), (699299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1069765232633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_4447
      · exact prime_fortyFiveAQ_699299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1069765232633) ^ 534882616316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069765232633) ^ 24878261224 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069765232633) ^ 240558856 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069765232633) ^ 1529768 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1157501278441 : Nat.Prime 1157501278441 := by
  apply lucas_primality 1157501278441 (11 : ZMod 1157501278441)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157501278441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_27481037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1157501278441) ^ 578750639220 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 385833759480 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 231500255688 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 89038559880 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 42120 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1193057399957 : Nat.Prime 1193057399957 := by
  apply lucas_primality 1193057399957 (2 : ZMod 1193057399957)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (389, 1), (5145949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (389, 1), (5145949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193057399957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_149
      · exact prime_fortyFiveAQ_389
      · exact prime_fortyFiveAQ_5145949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1193057399957) ^ 596528699978 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193057399957) ^ 8007096644 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193057399957) ^ 3066985604 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193057399957) ^ 231844 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_397
      · exact prime_fortyFiveAQ_977
      · exact prime_fortyFiveAQ_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_35279
      · exact prime_fortyFiveAQ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2704823010871 : Nat.Prime 2704823010871 := by
  apply lucas_primality 2704823010871 (13 : ZMod 2704823010871)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod) = 2704823010871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_90160767029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2704823010871) ^ 1352411505435 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 901607670290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 540964602174 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 30 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_761
      · exact prime_fortyFiveAQ_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3074820748067 : Nat.Prime 3074820748067 := by
  apply lucas_primality 3074820748067 (2 : ZMod 3074820748067)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074820748067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_103
      · exact prime_fortyFiveAQ_86843
      · exact prime_fortyFiveAQ_171877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3074820748067) ^ 1537410374033 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 29852628622 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 35406662 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 17889658 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3620174311723 : Nat.Prime 3620174311723 := by
  apply lucas_primality 3620174311723 (3 : ZMod 3620174311723)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (603362385287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (603362385287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3620174311723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_603362385287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3620174311723) ^ 1810087155861 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3620174311723) ^ 1206724770574 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3620174311723) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_381559
      · exact prime_fortyFiveAQ_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7216984001791 : Nat.Prime 7216984001791 := by
  apply lucas_primality 7216984001791 (3 : ZMod 7216984001791)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (37, 1), (722420821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (37, 1), (722420821, 1)] : List FactorBlock).map factorBlockValue).prod) = 7216984001791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_722420821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7216984001791) ^ 3608492000895 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7216984001791) ^ 2405661333930 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7216984001791) ^ 1443396800358 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7216984001791) ^ 195053621670 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7216984001791) ^ 9990 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7621129842719 : Nat.Prime 7621129842719 := by
  apply lucas_primality 7621129842719 (7 : ZMod 7621129842719)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (97, 1), (1097, 1), (300929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (97, 1), (1097, 1), (300929, 1)] : List FactorBlock).map factorBlockValue).prod) = 7621129842719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_97
      · exact prime_fortyFiveAQ_1097
      · exact prime_fortyFiveAQ_300929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7621129842719) ^ 3810564921359 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7621129842719) ^ 1088732834674 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7621129842719) ^ 448301755454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7621129842719) ^ 78568348894 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7621129842719) ^ 6947246894 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 7621129842719) ^ 25325342 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_8675153813089 : Nat.Prime 8675153813089 := by
  apply lucas_primality 8675153813089 (19 : ZMod 8675153813089)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (47, 1), (2269, 1), (40351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (47, 1), (2269, 1), (40351, 1)] : List FactorBlock).map factorBlockValue).prod) = 8675153813089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_2269
      · exact prime_fortyFiveAQ_40351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 8675153813089) ^ 4337576906544 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 8675153813089) ^ 2891717937696 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 8675153813089) ^ 1239307687584 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 8675153813089) ^ 184577740704 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 8675153813089) ^ 3823337952 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 8675153813089) ^ 214992288 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_11667194351249 : Nat.Prime 11667194351249 := by
  apply lucas_primality 11667194351249 (6 : ZMod 11667194351249)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (61, 1), (173, 1), (3636779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (61, 1), (173, 1), (3636779, 1)] : List FactorBlock).map factorBlockValue).prod) = 11667194351249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_61
      · exact prime_fortyFiveAQ_173
      · exact prime_fortyFiveAQ_3636779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11667194351249) ^ 5833597175624 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 11667194351249) ^ 614062860592 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 11667194351249) ^ 191265481168 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 11667194351249) ^ 67440429776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 11667194351249) ^ 3208112 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_13213323856003 : Nat.Prime 13213323856003 := by
  apply lucas_primality 13213323856003 (2 : ZMod 13213323856003)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod) = 13213323856003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_127
      · exact prime_fortyFiveAQ_383
      · exact prime_fortyFiveAQ_45274987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13213323856003) ^ 6606661928001 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 4404441285334 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 104041920126 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 34499540094 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 291846 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_13898969654707 : Nat.Prime 13898969654707 := by
  apply lucas_primality 13898969654707 (3 : ZMod 13898969654707)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (257388326939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (257388326939, 1)] : List FactorBlock).map factorBlockValue).prod) = 13898969654707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_257388326939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13898969654707) ^ 6949484827353 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13898969654707) ^ 4632989884902 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13898969654707) ^ 54 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod) = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_9281
      · exact prime_fortyFiveAQ_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_15242259685439 : Nat.Prime 15242259685439 := by
  apply lucas_primality 15242259685439 (13 : ZMod 15242259685439)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7621129842719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7621129842719, 1)] : List FactorBlock).map factorBlockValue).prod) = 15242259685439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7621129842719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 15242259685439) ^ 7621129842719 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 15242259685439) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_15677818679099 : Nat.Prime 15677818679099 := by
  apply lucas_primality 15677818679099 (2 : ZMod 15677818679099)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (761, 1), (81108667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (761, 1), (81108667, 1)] : List FactorBlock).map factorBlockValue).prod) = 15677818679099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_127
      · exact prime_fortyFiveAQ_761
      · exact prime_fortyFiveAQ_81108667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15677818679099) ^ 7838909339549 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15677818679099) ^ 123447391174 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15677818679099) ^ 20601601418 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 15677818679099) ^ 193294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_16702803599399 : Nat.Prime 16702803599399 := by
  apply lucas_primality 16702803599399 (7 : ZMod 16702803599399)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1193057399957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1193057399957, 1)] : List FactorBlock).map factorBlockValue).prod) = 16702803599399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_1193057399957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 16702803599399) ^ 8351401799699 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16702803599399) ^ 2386114799914 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16702803599399) ^ 14 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_16744068585947 : Nat.Prime 16744068585947 := by
  apply lucas_primality 16744068585947 (2 : ZMod 16744068585947)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod) = 16744068585947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_4789
      · exact prime_fortyFiveAQ_7910317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16744068585947) ^ 8372034292973 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 1288005275842 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 984945210938 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 3496360114 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 2116738 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_19000234857379 : Nat.Prime 19000234857379 := by
  apply lucas_primality 19000234857379 (2 : ZMod 19000234857379)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (947, 1), (3343934329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (947, 1), (3343934329, 1)] : List FactorBlock).map factorBlockValue).prod) = 19000234857379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_947
      · exact prime_fortyFiveAQ_3343934329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19000234857379) ^ 9500117428689 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19000234857379) ^ 6333411619126 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19000234857379) ^ 20063605974 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19000234857379) ^ 5682 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_19090862195893 : Nat.Prime 19090862195893 := by
  apply lucas_primality 19090862195893 (2 : ZMod 19090862195893)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod) = 19090862195893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_93582657823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19090862195893) ^ 9545431097946 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 6363620731964 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 1122991893876 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 204 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod) = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_21673431885071 : Nat.Prime 21673431885071 := by
  apply lucas_primality 21673431885071 (13 : ZMod 21673431885071)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) = 21673431885071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_3413
      · exact prime_fortyFiveAQ_3583
      · exact prime_fortyFiveAQ_3617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 21673431885071) ^ 10836715942535 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 4334686377014 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 3096204555010 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6350258390 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6048962290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 5992101710 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_26511385923637 : Nat.Prime 26511385923637 := by
  apply lucas_primality 26511385923637 (5 : ZMod 26511385923637)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (769, 1), (151206773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (769, 1), (151206773, 1)] : List FactorBlock).map factorBlockValue).prod) = 26511385923637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_769
      · exact prime_fortyFiveAQ_151206773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26511385923637) ^ 13255692961818 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 26511385923637) ^ 8837128641212 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 26511385923637) ^ 1395336101244 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 26511385923637) ^ 34475144244 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 26511385923637) ^ 175332 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_40671203078189 : Nat.Prime 40671203078189 := by
  apply lucas_primality 40671203078189 (2 : ZMod 40671203078189)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (5783, 1), (26242127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (5783, 1), (26242127, 1)] : List FactorBlock).map factorBlockValue).prod) = 40671203078189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_67
      · exact prime_fortyFiveAQ_5783
      · exact prime_fortyFiveAQ_26242127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40671203078189) ^ 20335601539094 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 40671203078189) ^ 607032881764 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 40671203078189) ^ 7032890036 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 40671203078189) ^ 1549844 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_43047490472939 : Nat.Prime 43047490472939 := by
  apply lucas_primality 43047490472939 (7 : ZMod 43047490472939)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod) = 43047490472939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_3074820748067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43047490472939) ^ 21523745236469 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 6149641496134 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 14 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_50184072854789 : Nat.Prime 50184072854789 := by
  apply lucas_primality 50184072854789 (2 : ZMod 50184072854789)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (27631, 1), (454055887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (27631, 1), (454055887, 1)] : List FactorBlock).map factorBlockValue).prod) = 50184072854789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_27631
      · exact prime_fortyFiveAQ_454055887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50184072854789) ^ 25092036427394 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50184072854789) ^ 1816223548 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50184072854789) ^ 110524 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_69689633870809 : Nat.Prime 69689633870809 := by
  apply lucas_primality 69689633870809 (17 : ZMod 69689633870809)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (47, 1), (53441, 1), (55051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (47, 1), (53441, 1), (55051, 1)] : List FactorBlock).map factorBlockValue).prod) = 69689633870809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_53441
      · exact prime_fortyFiveAQ_55051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 69689633870809) ^ 34844816935404 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 69689633870809) ^ 23229877956936 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 69689633870809) ^ 9955661981544 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 69689633870809) ^ 1482758167464 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 69689633870809) ^ 1304048088 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 69689633870809) ^ 1265910408 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_117753233405729 : Nat.Prime 117753233405729 := by
  apply lucas_primality 117753233405729 (3 : ZMod 117753233405729)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (163927, 1), (22447727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (163927, 1), (22447727, 1)] : List FactorBlock).map factorBlockValue).prod) = 117753233405729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_163927
      · exact prime_fortyFiveAQ_22447727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 117753233405729) ^ 58876616702864 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 117753233405729) ^ 718327264 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 117753233405729) ^ 5245664 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_229090346350717 : Nat.Prime 229090346350717 := by
  apply lucas_primality 229090346350717 (2 : ZMod 229090346350717)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod) = 229090346350717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19090862195893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229090346350717) ^ 114545173175358 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 76363448783572 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 12 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_1163
      · exact prime_fortyFiveAQ_1663
      · exact prime_fortyFiveAQ_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod) = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_443
      · exact prime_fortyFiveAQ_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_379646801290931 : Nat.Prime 379646801290931 := by
  apply lucas_primality 379646801290931 (2 : ZMod 379646801290931)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (14869, 1), (2553277297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (14869, 1), (2553277297, 1)] : List FactorBlock).map factorBlockValue).prod) = 379646801290931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_14869
      · exact prime_fortyFiveAQ_2553277297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 379646801290931) ^ 189823400645465 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 379646801290931) ^ 75929360258186 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 379646801290931) ^ 25532772970 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 379646801290931) ^ 148690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod) = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_444482290653677 : Nat.Prime 444482290653677 := by
  apply lucas_primality 444482290653677 (2 : ZMod 444482290653677)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (47, 1), (105107, 1), (2044901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (47, 1), (105107, 1), (2044901, 1)] : List FactorBlock).map factorBlockValue).prod) = 444482290653677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_105107
      · exact prime_fortyFiveAQ_2044901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 444482290653677) ^ 222241145326838 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444482290653677) ^ 40407480968516 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444482290653677) ^ 9457070013908 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444482290653677) ^ 4228855268 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444482290653677) ^ 217361276 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_562924752139699 : Nat.Prime 562924752139699 := by
  apply lucas_primality 562924752139699 (3 : ZMod 562924752139699)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (7216984001791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (7216984001791, 1)] : List FactorBlock).map factorBlockValue).prod) = 562924752139699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_7216984001791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 562924752139699) ^ 281462376069849 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 562924752139699) ^ 187641584046566 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 562924752139699) ^ 43301904010746 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 562924752139699) ^ 78 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod) = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_347
      · exact prime_fortyFiveAQ_109481
      · exact prime_fortyFiveAQ_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1403751053873449 : Nat.Prime 1403751053873449 := by
  apply lucas_primality 1403751053873449 (11 : ZMod 1403751053873449)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (19, 1), (146590544473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (19, 1), (146590544473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403751053873449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_146590544473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1403751053873449) ^ 701875526936724 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1403751053873449) ^ 467917017957816 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1403751053873449) ^ 200535864839064 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1403751053873449) ^ 73881634414392 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1403751053873449) ^ 9576 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1636728584473709 : Nat.Prime 1636728584473709 := by
  apply lucas_primality 1636728584473709 (2 : ZMod 1636728584473709)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2179291, 1), (17069027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2179291, 1), (17069027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1636728584473709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_2179291
      · exact prime_fortyFiveAQ_17069027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1636728584473709) ^ 818364292236854 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1636728584473709) ^ 148793507679428 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1636728584473709) ^ 751037188 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1636728584473709) ^ 95888804 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1793775758729587 : Nat.Prime 1793775758729587 := by
  apply lucas_primality 1793775758729587 (2 : ZMod 1793775758729587)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1793775758729587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_26921
      · exact prime_fortyFiveAQ_96293
      · exact prime_fortyFiveAQ_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1793775758729587) ^ 896887879364793 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 597925252909862 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 66631096866 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 18628309002 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 15553823118 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2286338952815851 : Nat.Prime 2286338952815851 := by
  apply lucas_primality 2286338952815851 (3 : ZMod 2286338952815851)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (15242259685439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (15242259685439, 1)] : List FactorBlock).map factorBlockValue).prod) = 2286338952815851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_15242259685439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2286338952815851) ^ 1143169476407925 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2286338952815851) ^ 762112984271950 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2286338952815851) ^ 457267790563170 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2286338952815851) ^ 150 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2539213503032641 : Nat.Prime 2539213503032641 := by
  apply lucas_primality 2539213503032641 (17 : ZMod 2539213503032641)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 2), (15643, 1), (3450737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 2), (15643, 1), (3450737, 1)] : List FactorBlock).map factorBlockValue).prod) = 2539213503032641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_15643
      · exact prime_fortyFiveAQ_3450737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2539213503032641) ^ 1269606751516320 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 2539213503032641) ^ 846404501010880 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 2539213503032641) ^ 507842700606528 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 2539213503032641) ^ 362744786147520 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 2539213503032641) ^ 162322668480 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 2539213503032641) ^ 735846720 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2563911177884773 : Nat.Prime 2563911177884773 := by
  apply lucas_primality 2563911177884773 (2 : ZMod 2563911177884773)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (219491, 1), (973430641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (219491, 1), (973430641, 1)] : List FactorBlock).map factorBlockValue).prod) = 2563911177884773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_219491
      · exact prime_fortyFiveAQ_973430641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2563911177884773) ^ 1281955588942386 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2563911177884773) ^ 854637059294924 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2563911177884773) ^ 11681167692 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2563911177884773) ^ 2633892 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_61
      · exact prime_fortyFiveAQ_67
      · exact prime_fortyFiveAQ_463
      · exact prime_fortyFiveAQ_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4209106507048549 : Nat.Prime 4209106507048549 := by
  apply lucas_primality 4209106507048549 (2 : ZMod 4209106507048549)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (16702803599399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (16702803599399, 1)] : List FactorBlock).map factorBlockValue).prod) = 4209106507048549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_16702803599399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4209106507048549) ^ 2104553253524274 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209106507048549) ^ 1403035502349516 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209106507048549) ^ 601300929578364 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209106507048549) ^ 252 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4648363849881439 : Nat.Prime 4648363849881439 := by
  apply lucas_primality 4648363849881439 (3 : ZMod 4648363849881439)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (257, 1), (15148257011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (257, 1), (15148257011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4648363849881439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_199
      · exact prime_fortyFiveAQ_257
      · exact prime_fortyFiveAQ_15148257011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4648363849881439) ^ 2324181924940719 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4648363849881439) ^ 1549454616627146 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4648363849881439) ^ 23358612310962 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4648363849881439) ^ 18087018871134 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4648363849881439) ^ 306858 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4825463586514099 : Nat.Prime 4825463586514099 := by
  apply lucas_primality 4825463586514099 (2 : ZMod 4825463586514099)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (761, 1), (2749, 1), (34949077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (761, 1), (2749, 1), (34949077, 1)] : List FactorBlock).map factorBlockValue).prod) = 4825463586514099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_761
      · exact prime_fortyFiveAQ_2749
      · exact prime_fortyFiveAQ_34949077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4825463586514099) ^ 2412731793257049 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4825463586514099) ^ 1608487862171366 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4825463586514099) ^ 438678507864918 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4825463586514099) ^ 6340950836418 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4825463586514099) ^ 1755352341402 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4825463586514099) ^ 138071274 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4847004293442769 : Nat.Prime 4847004293442769 := by
  apply lucas_primality 4847004293442769 (7 : ZMod 4847004293442769)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod) = 4847004293442769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_503
      · exact prime_fortyFiveAQ_66917996099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4847004293442769) ^ 2423502146721384 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 1615668097814256 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 9636191438256 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 72432 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod) = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_7127822871692591 : Nat.Prime 7127822871692591 := by
  apply lucas_primality 7127822871692591 (17 : ZMod 7127822871692591)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (149, 1), (67377094921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (149, 1), (67377094921, 1)] : List FactorBlock).map factorBlockValue).prod) = 7127822871692591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_71
      · exact prime_fortyFiveAQ_149
      · exact prime_fortyFiveAQ_67377094921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7127822871692591) ^ 3563911435846295 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 7127822871692591) ^ 1425564574338518 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 7127822871692591) ^ 100391871432290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 7127822871692591) ^ 47837737393910 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (17 : ZMod 7127822871692591) ^ 105790 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_11306594455736543 : Nat.Prime 11306594455736543 := by
  apply lucas_primality 11306594455736543 (5 : ZMod 11306594455736543)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (40671203078189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (40671203078189, 1)] : List FactorBlock).map factorBlockValue).prod) = 11306594455736543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_139
      · exact prime_fortyFiveAQ_40671203078189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11306594455736543) ^ 5653297227868271 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11306594455736543) ^ 81342406156378 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11306594455736543) ^ 278 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_81047
      · exact prime_fortyFiveAQ_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod) = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_223
      · exact prime_fortyFiveAQ_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_18287240216708153 : Nat.Prime 18287240216708153 := by
  apply lucas_primality 18287240216708153 (3 : ZMod 18287240216708153)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod) = 18287240216708153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_173
      · exact prime_fortyFiveAQ_13213323856003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18287240216708153) ^ 9143620108354076 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 105706590848024 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 1384 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_18401009513612249 : Nat.Prime 18401009513612249 := by
  apply lucas_primality 18401009513612249 (3 : ZMod 18401009513612249)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (43, 1), (181, 1), (827, 1), (11527561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (43, 1), (181, 1), (827, 1), (11527561, 1)] : List FactorBlock).map factorBlockValue).prod) = 18401009513612249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_181
      · exact prime_fortyFiveAQ_827
      · exact prime_fortyFiveAQ_11527561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18401009513612249) ^ 9200504756806124 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18401009513612249) ^ 593580952052008 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18401009513612249) ^ 427930453804936 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18401009513612249) ^ 101663035986808 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18401009513612249) ^ 22250313801224 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 18401009513612249) ^ 1596262168 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_21561233991609937 : Nat.Prime 21561233991609937 := by
  apply lucas_primality 21561233991609937 (5 : ZMod 21561233991609937)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 2), (17, 1), (64793, 1), (2413063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 2), (17, 1), (64793, 1), (2413063, 1)] : List FactorBlock).map factorBlockValue).prod) = 21561233991609937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_64793
      · exact prime_fortyFiveAQ_2413063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21561233991609937) ^ 10780616995804968 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21561233991609937) ^ 7187077997203312 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21561233991609937) ^ 1658556460893072 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21561233991609937) ^ 1268307881859408 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21561233991609937) ^ 332771039952 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21561233991609937) ^ 8935213872 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_24490011939472127 : Nat.Prime 24490011939472127 := by
  apply lucas_primality 24490011939472127 (5 : ZMod 24490011939472127)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod) = 24490011939472127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_67
      · exact prime_fortyFiveAQ_1877
      · exact prime_fortyFiveAQ_97368824257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24490011939472127) ^ 12245005969736063 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 365522566260778 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 13047422450438 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 251518 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_656951
      · exact prime_fortyFiveAQ_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_33936416144220883 : Nat.Prime 33936416144220883 := by
  apply lucas_primality 33936416144220883 (3 : ZMod 33936416144220883)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (4733, 1), (11602217353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (4733, 1), (11602217353, 1)] : List FactorBlock).map factorBlockValue).prod) = 33936416144220883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_103
      · exact prime_fortyFiveAQ_4733
      · exact prime_fortyFiveAQ_11602217353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33936416144220883) ^ 16968208072110441 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33936416144220883) ^ 11312138714740294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33936416144220883) ^ 329479768390494 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33936416144220883) ^ 7170170324154 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33936416144220883) ^ 2924994 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_36574480433416307 : Nat.Prime 36574480433416307 := by
  apply lucas_primality 36574480433416307 (2 : ZMod 36574480433416307)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod) = 36574480433416307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_18287240216708153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36574480433416307) ^ 18287240216708153 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36574480433416307) ^ 2 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_48169002919425847 : Nat.Prime 48169002919425847 := by
  apply lucas_primality 48169002919425847 (3 : ZMod 48169002919425847)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (241, 1), (3931, 1), (56120221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (241, 1), (3931, 1), (56120221, 1)] : List FactorBlock).map factorBlockValue).prod) = 48169002919425847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_151
      · exact prime_fortyFiveAQ_241
      · exact prime_fortyFiveAQ_3931
      · exact prime_fortyFiveAQ_56120221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48169002919425847) ^ 24084501459712923 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48169002919425847) ^ 16056334306475282 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48169002919425847) ^ 319000019333946 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48169002919425847) ^ 199871381408406 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48169002919425847) ^ 12253625774466 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48169002919425847) ^ 858318126 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_73751906302452347 : Nat.Prime 73751906302452347 := by
  apply lucas_primality 73751906302452347 (2 : ZMod 73751906302452347)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod) = 73751906302452347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_173
      · exact prime_fortyFiveAQ_12864823
      · exact prime_fortyFiveAQ_16568887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73751906302452347) ^ 36875953151226173 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 426311597124002 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 5732834902 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 4451228758 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_79260268916324227 : Nat.Prime 79260268916324227 := by
  apply lucas_primality 79260268916324227 (2 : ZMod 79260268916324227)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (4073, 1), (11222562643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (4073, 1), (11222562643, 1)] : List FactorBlock).map factorBlockValue).prod) = 79260268916324227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_4073
      · exact prime_fortyFiveAQ_11222562643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79260268916324227) ^ 39630134458162113 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79260268916324227) ^ 26420089638774742 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79260268916324227) ^ 4662368759783778 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79260268916324227) ^ 19459923622962 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79260268916324227) ^ 7062582 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_168555758635391581 : Nat.Prime 168555758635391581 := by
  apply lucas_primality 168555758635391581 (2 : ZMod 168555758635391581)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (3943, 1), (237489444917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (3943, 1), (237489444917, 1)] : List FactorBlock).map factorBlockValue).prod) = 168555758635391581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_3943
      · exact prime_fortyFiveAQ_237489444917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168555758635391581) ^ 84277879317695790 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 168555758635391581) ^ 56185252878463860 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 168555758635391581) ^ 33711151727078316 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 168555758635391581) ^ 42748100085060 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 168555758635391581) ^ 709740 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_246251221202136779 : Nat.Prime 246251221202136779 := by
  apply lucas_primality 246251221202136779 (2 : ZMod 246251221202136779)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6473, 1), (40193, 1), (473251901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6473, 1), (40193, 1), (473251901, 1)] : List FactorBlock).map factorBlockValue).prod) = 246251221202136779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_6473
      · exact prime_fortyFiveAQ_40193
      · exact prime_fortyFiveAQ_473251901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 246251221202136779) ^ 123125610601068389 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 246251221202136779) ^ 38042827313786 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 246251221202136779) ^ 6126719110346 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 246251221202136779) ^ 520338578 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_377440396466729153 : Nat.Prime 377440396466729153 := by
  apply lucas_primality 377440396466729153 (3 : ZMod 377440396466729153)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod) = 377440396466729153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_137
      · exact prime_fortyFiveAQ_43047490472939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377440396466729153) ^ 188720198233364576 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 2755039390268096 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 8768 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_61717
      · exact prime_fortyFiveAQ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_676208854926060779 : Nat.Prime 676208854926060779 := by
  apply lucas_primality 676208854926060779 (2 : ZMod 676208854926060779)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (113, 1), (2447, 1), (174678882557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (113, 1), (2447, 1), (174678882557, 1)] : List FactorBlock).map factorBlockValue).prod) = 676208854926060779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_113
      · exact prime_fortyFiveAQ_2447
      · exact prime_fortyFiveAQ_174678882557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 676208854926060779) ^ 338104427463030389 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 676208854926060779) ^ 96601264989437254 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 676208854926060779) ^ 5984149158637706 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 676208854926060779) ^ 276341992205174 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 676208854926060779) ^ 3871154 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_724366096863096349 : Nat.Prime 724366096863096349 := by
  apply lucas_primality 724366096863096349 (2 : ZMod 724366096863096349)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (53, 1), (379646801290931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (53, 1), (379646801290931, 1)] : List FactorBlock).map factorBlockValue).prod) = 724366096863096349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_379646801290931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 724366096863096349) ^ 362183048431548174 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 724366096863096349) ^ 241455365621032116 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 724366096863096349) ^ 13667284846473516 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 724366096863096349) ^ 1908 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_783019623353225509 : Nat.Prime 783019623353225509 := by
  apply lucas_primality 783019623353225509 (2 : ZMod 783019623353225509)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod) = 783019623353225509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_433
      · exact prime_fortyFiveAQ_16744068585947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 783019623353225509) ^ 391509811676612754 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 261006541117741836 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 1808359407282276 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 46764 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1052788358341308167 : Nat.Prime 1052788358341308167 := by
  apply lucas_primality 1052788358341308167 (5 : ZMod 1052788358341308167)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (17581, 1), (1032451135867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (17581, 1), (1032451135867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052788358341308167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_17581
      · exact prime_fortyFiveAQ_1032451135867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1052788358341308167) ^ 526394179170654083 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1052788358341308167) ^ 36303046839355454 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1052788358341308167) ^ 59882165880286 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1052788358341308167) ^ 1019698 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1511635180256161967 : Nat.Prime 1511635180256161967 := by
  apply lucas_primality 1511635180256161967 (5 : ZMod 1511635180256161967)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511635180256161967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_811
      · exact prime_fortyFiveAQ_21673431885071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1511635180256161967) ^ 755817590128080983 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 35154306517585162 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 1863915142116106 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 69746 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3613617964505360969 : Nat.Prime 3613617964505360969 := by
  apply lucas_primality 3613617964505360969 (3 : ZMod 3613617964505360969)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (165463, 1), (209994540059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (165463, 1), (209994540059, 1)] : List FactorBlock).map factorBlockValue).prod) = 3613617964505360969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_165463
      · exact prime_fortyFiveAQ_209994540059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3613617964505360969) ^ 1806808982252680484 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3613617964505360969) ^ 277970612654258536 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3613617964505360969) ^ 21839432166136 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3613617964505360969) ^ 17208152 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_12105047956497918193 : Nat.Prime 12105047956497918193 := by
  apply lucas_primality 12105047956497918193 (5 : ZMod 12105047956497918193)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (107, 1), (283, 1), (593, 1), (28517, 1), (54721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (107, 1), (283, 1), (593, 1), (28517, 1), (54721, 1)] : List FactorBlock).map factorBlockValue).prod) = 12105047956497918193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_107
      · exact prime_fortyFiveAQ_283
      · exact prime_fortyFiveAQ_593
      · exact prime_fortyFiveAQ_28517
      · exact prime_fortyFiveAQ_54721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12105047956497918193) ^ 6052523978248959096 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 4035015985499306064 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 113131289313064656 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 42774021047695824 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 20413234327989744 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 424485323017776 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 12105047956497918193) ^ 221213939008752 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_13080701940447819211 : Nat.Prime 13080701940447819211 := by
  apply lucas_primality 13080701940447819211 (10 : ZMod 13080701940447819211)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod) = 13080701940447819211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_2497849
      · exact prime_fortyFiveAQ_1032896747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13080701940447819211) ^ 6540350970223909605 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 4360233980149273070 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 2616140388089563842 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 1006207841572909170 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 5236786507290 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 12664094430 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod) = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_821
      · exact prime_fortyFiveAQ_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_65290371830632690583 : Nat.Prime 65290371830632690583 := by
  apply lucas_primality 65290371830632690583 (5 : ZMod 65290371830632690583)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod) = 65290371830632690583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_24490011939472127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65290371830632690583) ^ 32645185915316345291 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2106141026794602922 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 1518380740247271874 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2666 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod) = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_33749
      · exact prime_fortyFiveAQ_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_171835974006756638989 : Nat.Prime 171835974006756638989 := by
  apply lucas_primality 171835974006756638989 (2 : ZMod 171835974006756638989)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 2), (1403751053873449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 2), (1403751053873449, 1)] : List FactorBlock).map factorBlockValue).prod) = 171835974006756638989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_101
      · exact prime_fortyFiveAQ_1403751053873449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 171835974006756638989) ^ 85917987003378319494 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171835974006756638989) ^ 57278658002252212996 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171835974006756638989) ^ 1701346277294620188 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171835974006756638989) ^ 122412 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_833937441514931870167 : Nat.Prime 833937441514931870167 := by
  apply lucas_primality 833937441514931870167 (6 : ZMod 833937441514931870167)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1871, 1), (53055053, 1), (73693313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1871, 1), (53055053, 1), (73693313, 1)] : List FactorBlock).map factorBlockValue).prod) = 833937441514931870167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_1871
      · exact prime_fortyFiveAQ_53055053
      · exact prime_fortyFiveAQ_73693313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 833937441514931870167) ^ 416968720757465935083 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 833937441514931870167) ^ 277979147171643956722 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 833937441514931870167) ^ 43891444290259572114 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 833937441514931870167) ^ 445717499473507146 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 833937441514931870167) ^ 15718341503022 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 833937441514931870167) ^ 11316324474582 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_107
      · exact prime_fortyFiveAQ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_4250673673138978518451 : Nat.Prime 4250673673138978518451 := by
  apply lucas_primality 4250673673138978518451 (7 : ZMod 4250673673138978518451)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (123581, 1), (160709, 1), (49201303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (123581, 1), (160709, 1), (49201303, 1)] : List FactorBlock).map factorBlockValue).prod) = 4250673673138978518451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_123581
      · exact prime_fortyFiveAQ_160709
      · exact prime_fortyFiveAQ_49201303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4250673673138978518451) ^ 2125336836569489259225 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 1416891224379659506150 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 850134734627795703690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 146574954246171673050 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 34395851086647450 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 26449506083287050 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4250673673138978518451) ^ 86393518341150 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_5003624649089591221003 : Nat.Prime 5003624649089591221003 := by
  apply lucas_primality 5003624649089591221003 (2 : ZMod 5003624649089591221003)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (833937441514931870167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (833937441514931870167, 1)] : List FactorBlock).map factorBlockValue).prod) = 5003624649089591221003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_833937441514931870167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5003624649089591221003) ^ 2501812324544795610501 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5003624649089591221003) ^ 1667874883029863740334 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5003624649089591221003) ^ 6 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_9524135213376787415371 : Nat.Prime 9524135213376787415371 := by
  apply lucas_primality 9524135213376787415371 (19 : ZMod 9524135213376787415371)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 3), (19, 2), (2563911177884773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 3), (19, 2), (2563911177884773, 1)] : List FactorBlock).map factorBlockValue).prod) = 9524135213376787415371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_2563911177884773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 9524135213376787415371) ^ 4762067606688393707685 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 9524135213376787415371) ^ 3174711737792262471790 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 9524135213376787415371) ^ 1904827042675357483074 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 9524135213376787415371) ^ 1360590744768112487910 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 9524135213376787415371) ^ 501270274388251969230 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (19 : ZMod 9524135213376787415371) ^ 3714690 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_40362221920582743251351 : Nat.Prime 40362221920582743251351 := by
  apply lucas_primality 40362221920582743251351 (13 : ZMod 40362221920582743251351)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (311, 1), (380845967, 1), (973637453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (311, 1), (380845967, 1), (973637453, 1)] : List FactorBlock).map factorBlockValue).prod) = 40362221920582743251351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_311
      · exact prime_fortyFiveAQ_380845967
      · exact prime_fortyFiveAQ_973637453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 40362221920582743251351) ^ 20181110960291371625675 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 40362221920582743251351) ^ 8072444384116548650270 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 40362221920582743251351) ^ 5766031702940391893050 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 40362221920582743251351) ^ 129782064053320717850 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 40362221920582743251351) ^ 105980436759050 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (13 : ZMod 40362221920582743251351) ^ 41455083507950 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_55014347432082082067563 : Nat.Prime 55014347432082082067563 := by
  apply lucas_primality 55014347432082082067563 (2 : ZMod 55014347432082082067563)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (2053, 1), (13339, 1), (189057509411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (2053, 1), (13339, 1), (189057509411, 1)] : List FactorBlock).map factorBlockValue).prod) = 55014347432082082067563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_2053
      · exact prime_fortyFiveAQ_13339
      · exact prime_fortyFiveAQ_189057509411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55014347432082082067563) ^ 27507173716041041033781 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 18338115810694027355854 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 7859192490297440295366 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 5001304312007462006142 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 2391928149220960089894 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 26797051842222153954 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 4124323220037640158 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 55014347432082082067563) ^ 290992659342 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod) = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_21580023643
      · exact prime_fortyFiveAQ_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod) = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_3616901
      · exact prime_fortyFiveAQ_5004841
      · exact prime_fortyFiveAQ_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_95241352133767874153711 : Nat.Prime 95241352133767874153711 := by
  apply lucas_primality 95241352133767874153711 (11 : ZMod 95241352133767874153711)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9524135213376787415371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9524135213376787415371, 1)] : List FactorBlock).map factorBlockValue).prod) = 95241352133767874153711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_9524135213376787415371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 95241352133767874153711) ^ 47620676066883937076855 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 95241352133767874153711) ^ 19048270426753574830742 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (11 : ZMod 95241352133767874153711) ^ 10 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_165806013621219257821763 : Nat.Prime 165806013621219257821763 := by
  apply lucas_primality 165806013621219257821763 (2 : ZMod 165806013621219257821763)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17834879, 1), (4648363849881439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17834879, 1), (4648363849881439, 1)] : List FactorBlock).map factorBlockValue).prod) = 165806013621219257821763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_17834879
      · exact prime_fortyFiveAQ_4648363849881439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 165806013621219257821763) ^ 82903006810609628910881 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 165806013621219257821763) ^ 9296727699762878 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 165806013621219257821763) ^ 35669758 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_173394724647282179600201 : Nat.Prime 173394724647282179600201 := by
  apply lucas_primality 173394724647282179600201 (6 : ZMod 173394724647282179600201)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (59, 1), (433, 1), (33936416144220883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (59, 1), (433, 1), (33936416144220883, 1)] : List FactorBlock).map factorBlockValue).prod) = 173394724647282179600201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_433
      · exact prime_fortyFiveAQ_33936416144220883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 173394724647282179600201) ^ 86697362323641089800100 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 173394724647282179600201) ^ 34678944929456435920040 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 173394724647282179600201) ^ 2938893638089528467800 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 173394724647282179600201) ^ 400449710501806419400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 173394724647282179600201) ^ 5109400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_217545305715774718420367 : Nat.Prime 217545305715774718420367 := by
  apply lucas_primality 217545305715774718420367 (5 : ZMod 217545305715774718420367)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (503, 1), (77551, 1), (11667194351249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (503, 1), (77551, 1), (11667194351249, 1)] : List FactorBlock).map factorBlockValue).prod) = 217545305715774718420367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_239
      · exact prime_fortyFiveAQ_503
      · exact prime_fortyFiveAQ_77551
      · exact prime_fortyFiveAQ_11667194351249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 217545305715774718420367) ^ 108772652857887359210183 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 217545305715774718420367) ^ 910231404668513466194 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 217545305715774718420367) ^ 432495637605913953122 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 217545305715774718420367) ^ 2805190206648202066 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 217545305715774718420367) ^ 18645897134 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_994132778694726848755723 : Nat.Prime 994132778694726848755723 := by
  apply lucas_primality 994132778694726848755723 (3 : ZMod 994132778694726848755723)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39364363, 1), (4209106507048549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39364363, 1), (4209106507048549, 1)] : List FactorBlock).map factorBlockValue).prod) = 994132778694726848755723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_39364363
      · exact prime_fortyFiveAQ_4209106507048549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 994132778694726848755723) ^ 497066389347363424377861 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 994132778694726848755723) ^ 331377592898242282918574 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 994132778694726848755723) ^ 25254639042291294 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (3 : ZMod 994132778694726848755723) ^ 236186178 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1139180544401246242944869 : Nat.Prime 1139180544401246242944869 := by
  apply lucas_primality 1139180544401246242944869 (2 : ZMod 1139180544401246242944869)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (4250673673138978518451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (4250673673138978518451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139180544401246242944869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_67
      · exact prime_fortyFiveAQ_4250673673138978518451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1139180544401246242944869) ^ 569590272200623121472434 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139180544401246242944869) ^ 17002694692555914073804 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139180544401246242944869) ^ 268 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1214352783196617334413989 : Nat.Prime 1214352783196617334413989 := by
  apply lucas_primality 1214352783196617334413989 (2 : ZMod 1214352783196617334413989)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (29, 1), (569, 1), (619, 1), (2286338952815851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (29, 1), (569, 1), (619, 1), (2286338952815851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214352783196617334413989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_569
      · exact prime_fortyFiveAQ_619
      · exact prime_fortyFiveAQ_2286338952815851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1214352783196617334413989) ^ 607176391598308667206994 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214352783196617334413989) ^ 93411752553585948801076 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214352783196617334413989) ^ 41874233903331632221172 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214352783196617334413989) ^ 2134187668183861747652 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214352783196617334413989) ^ 1961797711141546582252 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214352783196617334413989) ^ 531134188 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_3866987191788559531764157 : Nat.Prime 3866987191788559531764157 := by
  apply lucas_primality 3866987191788559531764157 (5 : ZMod 3866987191788559531764157)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod) = 3866987191788559531764157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_8810759
      · exact prime_fortyFiveAQ_36574480433416307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3866987191788559531764157) ^ 1933493595894279765882078 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 1288995730596186510588052 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 438893765200995684 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 105729108 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_10719727943708845867018189 : Nat.Prime 10719727943708845867018189 := by
  apply lucas_primality 10719727943708845867018189 (6 : ZMod 10719727943708845867018189)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (887, 1), (1439, 1), (3209, 1), (279073, 1), (13245811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (887, 1), (1439, 1), (3209, 1), (279073, 1), (13245811, 1)] : List FactorBlock).map factorBlockValue).prod) = 10719727943708845867018189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_887
      · exact prime_fortyFiveAQ_1439
      · exact prime_fortyFiveAQ_3209
      · exact prime_fortyFiveAQ_279073
      · exact prime_fortyFiveAQ_13245811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10719727943708845867018189) ^ 5359863971854422933509094 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 3573242647902948622339396 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 181690304130658404525732 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 12085375359310987448724 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 7449428730860907482292 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 3340519770554330279532 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 38411913526958343756 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10719727943708845867018189) ^ 809291929630344708 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod) = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_97
      · exact prime_fortyFiveAQ_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_565978827496031936574588001 : Nat.Prime 565978827496031936574588001 := by
  apply lucas_primality 565978827496031936574588001 (73 : ZMod 565978827496031936574588001)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 5), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 5), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 565978827496031936574588001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 565978827496031936574588001) ^ 282989413748015968287294000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 188659609165343978858196000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 113195765499206387314917600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 80854118213718848082084000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 51452620681457448779508000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 43536832884310148967276000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 33292872205648937445564000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 29788359341896417714452000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 24607775108523127677156000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 19516511292966618502572000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 18257381532130062470148000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 15296725067460322610124000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 13804361646244681379868000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 13162298313861207827316000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 10678845801811923331596000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 9592861482983592145332000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (73 : ZMod 565978827496031936574588001) ^ 9278341434361179288108000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_625905997466200023976603201 : Nat.Prime 625905997466200023976603201 := by
  apply lucas_primality 625905997466200023976603201 (79 : ZMod 625905997466200023976603201)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 625905997466200023976603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 625905997466200023976603201) ^ 312952998733100011988301600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 208635332488733341325534400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 125181199493240004795320640 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 89415142495171431996657600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 56900545224200002179691200 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 48146615189707694152046400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 32942420919273685472452800 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 27213304237660870607678400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 21582965429868966344020800 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 20190516047296774966987200 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 16916378309897297945313600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 15265999938200000584795200 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 14555953429446512185502400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 13317148882259574978225600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 11809547122003774037294400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10608576228240678372484800 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10260754056822951212731200 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_633357259340797643309658001 : Nat.Prime 633357259340797643309658001 := by
  apply lucas_primality 633357259340797643309658001 (101 : ZMod 633357259340797643309658001)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 633357259340797643309658001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 633357259340797643309658001) ^ 316678629670398821654829000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 211119086446932547769886000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 126671451868159528661931600 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 90479608477256806187094000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 57577932667345240300878000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 48719789180061357177666000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 37256309372988096665274000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 33334592596884086489982000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 27537272145252071448246000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 21839905494510263562402000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 20430879333574117526118000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 17117763765967503873234000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 15447738032702381544138000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 14729238589320875425806000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 13475686368953141347014000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 11950136968694295156786000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10734868802386400734062000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10382905890832748250978000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_5
      · exact prime_fortyFiveAQ_7
      · exact prime_fortyFiveAQ_11
      · exact prime_fortyFiveAQ_13
      · exact prime_fortyFiveAQ_17
      · exact prime_fortyFiveAQ_19
      · exact prime_fortyFiveAQ_23
      · exact prime_fortyFiveAQ_29
      · exact prime_fortyFiveAQ_31
      · exact prime_fortyFiveAQ_37
      · exact prime_fortyFiveAQ_41
      · exact prime_fortyFiveAQ_43
      · exact prime_fortyFiveAQ_47
      · exact prime_fortyFiveAQ_53
      · exact prime_fortyFiveAQ_59
      · exact prime_fortyFiveAQ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem prime_fortyFiveAQ_53202009784627002038011272073 : Nat.Prime 53202009784627002038011272073 := by
  apply lucas_primality 53202009784627002038011272073 (10 : ZMod 53202009784627002038011272073)
  · rw [← fortyFiveAQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyFiveAQ_2
      · exact prime_fortyFiveAQ_3
      · exact prime_fortyFiveAQ_83
      · exact prime_fortyFiveAQ_1433741
      · exact prime_fortyFiveAQ_106163831
      · exact prime_fortyFiveAQ_58488456857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 53202009784627002038011272073) ^ 26601004892313501019005636036 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 53202009784627002038011272073) ^ 17734003261542334012670424024 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 53202009784627002038011272073) ^ 640988069694301229373629784 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 53202009784627002038011272073) ^ 37107127287722818861992 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 53202009784627002038011272073) ^ 501131216568729533112 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide
    · change (10 : ZMod 53202009784627002038011272073) ^ 909615548837303496 ≠ 1
      rw [← fortyFiveAQFastPow_eq_pow]
      decide

private theorem phi_fortyFiveAQ_53202009784627002038011272000 : Nat.totient 53202009784627002038011272000 = 7000711580671228772352000000 := by
  rw [← show ((([(2, 6), (3, 5), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_7, prime_fortyFiveAQ_11, prime_fortyFiveAQ_13, prime_fortyFiveAQ_17, prime_fortyFiveAQ_19, prime_fortyFiveAQ_23, prime_fortyFiveAQ_29, prime_fortyFiveAQ_31, prime_fortyFiveAQ_37, prime_fortyFiveAQ_41, prime_fortyFiveAQ_43, prime_fortyFiveAQ_47, prime_fortyFiveAQ_53, prime_fortyFiveAQ_59, prime_fortyFiveAQ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272001 : Nat.totient 53202009784627002038011272001 = 52919934434845687915233762240 := by
  rw [← show ((([(263, 1), (1279, 1), (1381, 1), (341996947, 1), (334877399159, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_263, prime_fortyFiveAQ_1279, prime_fortyFiveAQ_1381, prime_fortyFiveAQ_341996947, prime_fortyFiveAQ_334877399159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272002 : Nat.totient 53202009784627002038011272002 = 26600954462561761028992610400 := by
  rw [← show ((([(2, 1), (611257, 1), (3848951, 1), (11306594455736543, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_611257, prime_fortyFiveAQ_3848951, prime_fortyFiveAQ_11306594455736543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272003 : Nat.totient 53202009784627002038011272003 = 35427815830920007170045901440 := by
  rw [← show ((([(3, 1), (883, 1), (1535377, 1), (13080701940447819211, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_883, prime_fortyFiveAQ_1535377, prime_fortyFiveAQ_13080701940447819211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272004 : Nat.totient 53202009784627002038011272004 = 26601004891820998468577512808 := by
  rw [← show ((([(2, 2), (54011924819, 1), (246251221202136779, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_54011924819, prime_fortyFiveAQ_246251221202136779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272005 : Nat.totient 53202009784627002038011272005 = 42416346367538797529281340608 := by
  rw [← show ((([(5, 1), (293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_293, prime_fortyFiveAQ_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272006 : Nat.totient 53202009784627002038011272006 = 17726269287158756893606891104 := by
  rw [← show ((([(2, 1), (3, 1), (2293, 1), (3866987191788559531764157, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_2293, prime_fortyFiveAQ_3866987191788559531764157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272007 : Nat.totient 53202009784627002038011272007 = 45537404304875177243093262624 := by
  rw [← show ((([(7, 1), (709, 1), (10719727943708845867018189, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_7, prime_fortyFiveAQ_709, prime_fortyFiveAQ_10719727943708845867018189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272008 : Nat.totient 53202009784627002038011272008 = 26440470169282728698446440000 := by
  rw [← show ((([(2, 3), (167, 1), (23251, 1), (240283, 1), (7127822871692591, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_167, prime_fortyFiveAQ_23251, prime_fortyFiveAQ_240283, prime_fortyFiveAQ_7127822871692591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272009 : Nat.totient 53202009784627002038011272009 = 35467759647446283316344663072 := by
  rw [← show ((([(3, 2), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_143669, prime_fortyFiveAQ_13852339783, prime_fortyFiveAQ_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272010 : Nat.totient 53202009784627002038011272010 = 21272809460526560612669875200 := by
  rw [← show ((([(2, 1), (5, 1), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_2663, prime_fortyFiveAQ_9063547, prime_fortyFiveAQ_26126021, prime_fortyFiveAQ_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272011 : Nat.totient 53202009784627002038011272011 = 48365214699358455728056793280 := by
  rw [← show ((([(11, 1), (202387, 1), (4952377, 1), (4825463586514099, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_11, prime_fortyFiveAQ_202387, prime_fortyFiveAQ_4952377, prime_fortyFiveAQ_4825463586514099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272012 : Nat.totient 53202009784627002038011272012 = 17660406267994430728807833600 := by
  rw [← show ((([(2, 2), (3, 1), (241, 1), (1701391, 1), (11484449, 1), (941489444879, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_241, prime_fortyFiveAQ_1701391, prime_fortyFiveAQ_11484449, prime_fortyFiveAQ_941489444879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272013 : Nat.totient 53202009784627002038011272013 = 49104211190210347682118041280 := by
  rw [← show ((([(13, 1), (9203, 1), (1000462471, 1), (444482290653677, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_13, prime_fortyFiveAQ_9203, prime_fortyFiveAQ_1000462471, prime_fortyFiveAQ_444482290653677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272014 : Nat.totient 53202009784627002038011272014 = 22800619162937191662687615000 := by
  rw [← show ((([(2, 1), (7, 1), (94151, 1), (40362221920582743251351, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_7, prime_fortyFiveAQ_94151, prime_fortyFiveAQ_40362221920582743251351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272015 : Nat.totient 53202009784627002038011272015 = 28374405217535255914709808800 := by
  rw [← show ((([(3, 1), (5, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_30429025931, prime_fortyFiveAQ_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272016 : Nat.totient 53202009784627002038011272016 = 26524322668198731876890388480 := by
  rw [← show ((([(2, 4), (347, 1), (1203121, 1), (120035339, 1), (66352936957, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_347, prime_fortyFiveAQ_1203121, prime_fortyFiveAQ_120035339, prime_fortyFiveAQ_66352936957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272017 : Nat.totient 53202009784627002038011272017 = 50072479796027836983719529792 := by
  rw [← show ((([(17, 1), (39484221163, 1), (79260268916324227, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_17, prime_fortyFiveAQ_39484221163, prime_fortyFiveAQ_79260268916324227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272018 : Nat.totient 53202009784627002038011272018 = 17650851454747358758890445824 := by
  rw [← show ((([(2, 1), (3, 2), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_223, prime_fortyFiveAQ_5113, prime_fortyFiveAQ_101287, prime_fortyFiveAQ_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272019 : Nat.totient 53202009784627002038011272019 = 50401881411054711031331026560 := by
  rw [← show ((([(19, 1), (2231587, 1), (5280703643, 1), (237612246161, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_19, prime_fortyFiveAQ_2231587, prime_fortyFiveAQ_5280703643, prime_fortyFiveAQ_237612246161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272020 : Nat.totient 53202009784627002038011272020 = 21272918339361761714570256384 := by
  rw [← show ((([(2, 2), (5, 1), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_3137, prime_fortyFiveAQ_19309, prime_fortyFiveAQ_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272021 : Nat.totient 53202009784627002038011272021 = 30168580721330707055057548800 := by
  rw [← show ((([(3, 1), (7, 1), (131, 1), (60607, 1), (275672333, 1), (1157501278441, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_7, prime_fortyFiveAQ_131, prime_fortyFiveAQ_60607, prime_fortyFiveAQ_275672333, prime_fortyFiveAQ_1157501278441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272022 : Nat.totient 53202009784627002038011272022 = 24181779306763663247626969000 := by
  rw [← show ((([(2, 1), (11, 1), (25391, 1), (95241352133767874153711, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_11, prime_fortyFiveAQ_25391, prime_fortyFiveAQ_95241352133767874153711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272023 : Nat.totient 53202009784627002038011272023 = 50888876686407123991493929920 := by
  rw [← show ((([(23, 1), (23218313, 1), (1113694831, 1), (89454735767, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_23, prime_fortyFiveAQ_23218313, prime_fortyFiveAQ_1113694831, prime_fortyFiveAQ_89454735767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272024 : Nat.totient 53202009784627002038011272024 = 17649107852257261929427200000 := by
  rw [← show ((([(2, 3), (3, 1), (211, 1), (28751, 1), (75389, 1), (4847004293442769, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_211, prime_fortyFiveAQ_28751, prime_fortyFiveAQ_75389, prime_fortyFiveAQ_4847004293442769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272025 : Nat.totient 53202009784627002038011272025 = 42547556222423221692744000000 := by
  rw [← show ((([(5, 2), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_3181, prime_fortyFiveAQ_73571, prime_fortyFiveAQ_455881, prime_fortyFiveAQ_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272026 : Nat.totient 53202009784627002038011272026 = 24552693010055156631388320000 := by
  rw [← show ((([(2, 1), (13, 1), (11801, 1), (173394724647282179600201, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_13, prime_fortyFiveAQ_11801, prime_fortyFiveAQ_173394724647282179600201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272027 : Nat.totient 53202009784627002038011272027 = 34982140363815519732633004800 := by
  rw [← show ((([(3, 3), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_73, prime_fortyFiveAQ_13737811, prime_fortyFiveAQ_68784581, prime_fortyFiveAQ_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272028 : Nat.totient 53202009784627002038011272028 = 22479721835741071014392717760 := by
  rw [← show ((([(2, 2), (7, 1), (71, 1), (36944819, 1), (724366096863096349, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_7, prime_fortyFiveAQ_71, prime_fortyFiveAQ_36944819, prime_fortyFiveAQ_724366096863096349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272029 : Nat.totient 53202009784627002038011272029 = 51367457504630339381782179840 := by
  rw [← show ((([(29, 1), (439346137, 1), (541395353, 1), (7712740241, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_29, prime_fortyFiveAQ_439346137, prime_fortyFiveAQ_541395353, prime_fortyFiveAQ_7712740241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272030 : Nat.totient 53202009784627002038011272030 = 14185326469577935538308700160 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_8233, prime_fortyFiveAQ_93811, prime_fortyFiveAQ_8274073, prime_fortyFiveAQ_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272031 : Nat.totient 53202009784627002038011272031 = 51188147586185871059118005760 := by
  rw [← show ((([(31, 1), (173, 1), (819509, 1), (12105047956497918193, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_31, prime_fortyFiveAQ_173, prime_fortyFiveAQ_819509, prime_fortyFiveAQ_12105047956497918193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272032 : Nat.totient 53202009784627002038011272032 = 26600995497048509774904072192 := by
  rw [← show ((([(2, 5), (2832133, 1), (12488895919, 1), (47004600913, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_2832133, prime_fortyFiveAQ_12488895919, prime_fortyFiveAQ_47004600913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272033 : Nat.totient 53202009784627002038011272033 = 32178939988460727934845648000 := by
  rw [← show ((([(3, 1), (11, 2), (499, 1), (375101, 1), (783019623353225509, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_11, prime_fortyFiveAQ_499, prime_fortyFiveAQ_375101, prime_fortyFiveAQ_783019623353225509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272034 : Nat.totient 53202009784627002038011272034 = 25036227342341937499822087680 := by
  rw [← show ((([(2, 1), (17, 1), (1994227, 1), (18395368441, 1), (42654616243, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_17, prime_fortyFiveAQ_1994227, prime_fortyFiveAQ_18395368441, prime_fortyFiveAQ_42654616243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272035 : Nat.totient 53202009784627002038011272035 = 35933880916332062412312301056 := by
  rw [← show ((([(5, 1), (7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_7, prime_fortyFiveAQ_67, prime_fortyFiveAQ_12583, prime_fortyFiveAQ_277259, prime_fortyFiveAQ_2674733, prime_fortyFiveAQ_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272036 : Nat.totient 53202009784627002038011272036 = 17734003261542334012670424000 := by
  rw [← show ((([(2, 2), (3, 2), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272037 : Nat.totient 53202009784627002038011272037 = 51617477061298756901972270592 := by
  rw [← show ((([(37, 1), (353, 1), (7236045083, 1), (562924752139699, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_37, prime_fortyFiveAQ_353, prime_fortyFiveAQ_7236045083, prime_fortyFiveAQ_562924752139699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272038 : Nat.totient 53202009784627002038011272038 = 25180446753445146954053362272 := by
  rw [← show ((([(2, 1), (19, 1), (1229, 1), (1139180544401246242944869, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_19, prime_fortyFiveAQ_1229, prime_fortyFiveAQ_1139180544401246242944869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272039 : Nat.totient 53202009784627002038011272039 = 32596693462453017141878856192 := by
  rw [← show ((([(3, 1), (13, 1), (229, 1), (887599, 1), (1779481213, 1), (3771531487, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_13, prime_fortyFiveAQ_229, prime_fortyFiveAQ_887599, prime_fortyFiveAQ_1779481213, prime_fortyFiveAQ_3771531487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272040 : Nat.totient 53202009784627002038011272040 = 21255709062173240278465873920 := by
  rw [← show ((([(2, 3), (5, 1), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_919, prime_fortyFiveAQ_11257, prime_fortyFiveAQ_425291, prime_fortyFiveAQ_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272041 : Nat.totient 53202009784627002038011272041 = 51904398178138855496455699200 := by
  rw [← show ((([(41, 1), (60652391, 1), (68674223, 1), (311531884057, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_41, prime_fortyFiveAQ_60652391, prime_fortyFiveAQ_68674223, prime_fortyFiveAQ_311531884057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272042 : Nat.totient 53202009784627002038011272042 = 15200158760185402606782934656 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (36587, 1), (107042151929, 1), (323442523387, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_7, prime_fortyFiveAQ_36587, prime_fortyFiveAQ_107042151929, prime_fortyFiveAQ_323442523387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272043 : Nat.totient 53202009784627002038011272043 = 51682167788498688705639782400 := by
  rw [← show ((([(43, 1), (197, 1), (3833, 1), (9721, 1), (168555758635391581, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_43, prime_fortyFiveAQ_197, prime_fortyFiveAQ_3833, prime_fortyFiveAQ_9721, prime_fortyFiveAQ_168555758635391581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272044 : Nat.totient 53202009784627002038011272044 = 24164396309746228274614191360 := by
  rw [← show ((([(2, 2), (11, 1), (1319, 1), (19031057, 1), (48169002919425847, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_11, prime_fortyFiveAQ_1319, prime_fortyFiveAQ_19031057, prime_fortyFiveAQ_48169002919425847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272045 : Nat.totient 53202009784627002038011272045 = 28093315868479095348023428608 := by
  rw [← show ((([(3, 2), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_103, prime_fortyFiveAQ_5009, prime_fortyFiveAQ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272046 : Nat.totient 53202009784627002038011272046 = 25192514315421868868877388800 := by
  rw [← show ((([(2, 1), (23, 1), (101, 1), (6996360289, 1), (1636728584473709, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_23, prime_fortyFiveAQ_101, prime_fortyFiveAQ_6996360289, prime_fortyFiveAQ_1636728584473709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272047 : Nat.totient 53202009784627002038011272047 = 52062425053008362079001980952 := by
  rw [← show ((([(47, 1), (6827, 1), (165806013621219257821763, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_47, prime_fortyFiveAQ_6827, prime_fortyFiveAQ_165806013621219257821763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272048 : Nat.totient 53202009784627002038011272048 = 17733958119216199282728546048 := by
  rw [← show ((([(2, 4), (3, 1), (406247, 1), (11909399, 1), (229090346350717, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_406247, prime_fortyFiveAQ_11909399, prime_fortyFiveAQ_229090346350717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272049 : Nat.totient 53202009784627002038011272049 = 45349774341213197339944316640 := by
  rw [← show ((([(7, 2), (181, 1), (8870999, 1), (676208854926060779, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_7, prime_fortyFiveAQ_181, prime_fortyFiveAQ_8870999, prime_fortyFiveAQ_676208854926060779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272050 : Nat.totient 53202009784627002038011272050 = 21091078975848841757548339200 := by
  rw [← show ((([(2, 1), (5, 2), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_139, prime_fortyFiveAQ_577, prime_fortyFiveAQ_2303321, prime_fortyFiveAQ_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272051 : Nat.totient 53202009784627002038011272051 = 33337787686950830645481753600 := by
  rw [← show ((([(3, 1), (17, 2), (761, 1), (29811610063, 1), (2704823010871, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_17, prime_fortyFiveAQ_761, prime_fortyFiveAQ_29811610063, prime_fortyFiveAQ_2704823010871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272052 : Nat.totient 53202009784627002038011272052 = 24549552659413745424301462368 := by
  rw [← show ((([(2, 2), (13, 1), (4703, 1), (217545305715774718420367, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_13, prime_fortyFiveAQ_4703, prime_fortyFiveAQ_217545305715774718420367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272053 : Nat.totient 53202009784627002038011272053 = 52198054409894637609013229568 := by
  rw [← show ((([(53, 1), (407633, 1), (7049167, 1), (7100183, 1), (49201177, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_53, prime_fortyFiveAQ_407633, prime_fortyFiveAQ_7049167, prime_fortyFiveAQ_7100183, prime_fortyFiveAQ_49201177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272054 : Nat.totient 53202009784627002038011272054 = 17642304484512080973900668928 := by
  rw [← show ((([(2, 1), (3, 3), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_283, prime_fortyFiveAQ_613, prime_fortyFiveAQ_85303, prime_fortyFiveAQ_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272055 : Nat.totient 53202009784627002038011272055 = 38432058222431911461495290880 := by
  rw [← show ((([(5, 1), (11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_11, prime_fortyFiveAQ_149, prime_fortyFiveAQ_60793, prime_fortyFiveAQ_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272056 : Nat.totient 53202009784627002038011272056 = 22799668205956507198815605760 := by
  rw [← show ((([(2, 3), (7, 1), (25183, 1), (161527, 1), (248243, 1), (551107, 1), (1707161, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_7, prime_fortyFiveAQ_25183, prime_fortyFiveAQ_161527, prime_fortyFiveAQ_248243, prime_fortyFiveAQ_551107, prime_fortyFiveAQ_1707161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272057 : Nat.totient 53202009784627002038011272057 = 33574564229588619580220866560 := by
  rw [← show ((([(3, 1), (19, 1), (2113, 1), (4871, 1), (11119, 1), (48179, 1), (230969, 1), (732923, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_19, prime_fortyFiveAQ_2113, prime_fortyFiveAQ_4871, prime_fortyFiveAQ_11119, prime_fortyFiveAQ_48179, prime_fortyFiveAQ_230969, prime_fortyFiveAQ_732923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272058 : Nat.totient 53202009784627002038011272058 = 25683719605821318824188842240 := by
  rw [← show ((([(2, 1), (29, 1), (3207473, 1), (20575691, 1), (13898969654707, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_29, prime_fortyFiveAQ_3207473, prime_fortyFiveAQ_20575691, prime_fortyFiveAQ_13898969654707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272059 : Nat.totient 53202009784627002038011272059 = 52248001941783888190100167680 := by
  rw [← show ((([(59, 1), (1249, 1), (5023, 1), (39702781, 1), (3620174311723, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_59, prime_fortyFiveAQ_1249, prime_fortyFiveAQ_5023, prime_fortyFiveAQ_39702781, prime_fortyFiveAQ_3620174311723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272060 : Nat.totient 53202009784627002038011272060 = 14160493283226141610141286400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_769, prime_fortyFiveAQ_2143, prime_fortyFiveAQ_8597, prime_fortyFiveAQ_9792301, prime_fortyFiveAQ_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272061 : Nat.totient 53202009784627002038011272061 = 52325121849488940852308491200 := by
  rw [← show ((([(61, 1), (13523, 1), (61261, 1), (1052788358341308167, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_61, prime_fortyFiveAQ_13523, prime_fortyFiveAQ_61261, prime_fortyFiveAQ_1052788358341308167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272062 : Nat.totient 53202009784627002038011272062 = 25733684407645252073978668800 := by
  rw [← show ((([(2, 1), (31, 1), (2791, 1), (2610980759, 1), (117753233405729, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_31, prime_fortyFiveAQ_2791, prime_fortyFiveAQ_2610980759, prime_fortyFiveAQ_117753233405729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272063 : Nat.totient 53202009784627002038011272063 = 30131557742477273191048396800 := by
  rw [← show ((([(3, 2), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_7, prime_fortyFiveAQ_113, prime_fortyFiveAQ_54421, prime_fortyFiveAQ_97654321, prime_fortyFiveAQ_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272064 : Nat.totient 53202009784627002038011272064 = 26601004892310800909911060992 := by
  rw [← show ((([(2, 7), (15677818679099, 1), (26511385923637, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_15677818679099, prime_fortyFiveAQ_26511385923637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272065 : Nat.totient 53202009784627002038011272065 = 39284218407544554285112737792 := by
  rw [← show ((([(5, 1), (13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_13, prime_fortyFiveAQ_11489, prime_fortyFiveAQ_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272066 : Nat.totient 53202009784627002038011272066 = 16077414553359780765826473600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (367, 1), (33641, 1), (65290371830632690583, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_11, prime_fortyFiveAQ_367, prime_fortyFiveAQ_33641, prime_fortyFiveAQ_65290371830632690583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272067 : Nat.totient 53202009784627002038011272067 = 53148324608204285963291595840 := by
  rw [← show ((([(991, 1), (1069765232633, 1), (50184072854789, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_991, prime_fortyFiveAQ_1069765232633, prime_fortyFiveAQ_50184072854789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272068 : Nat.totient 53202009784627002038011272068 = 25004427649729769699903919744 := by
  rw [← show ((([(2, 2), (17, 1), (787, 1), (994132778694726848755723, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_17, prime_fortyFiveAQ_787, prime_fortyFiveAQ_994132778694726848755723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272069 : Nat.totient 53202009784627002038011272069 = 33496476666092846137348531200 := by
  rw [← show ((([(3, 1), (23, 1), (79, 1), (82621199, 1), (325800521, 1), (362583961, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_23, prime_fortyFiveAQ_79, prime_fortyFiveAQ_82621199, prime_fortyFiveAQ_325800521, prime_fortyFiveAQ_362583961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272070 : Nat.totient 53202009784627002038011272070 = 18174838203281357432562309120 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_7, prime_fortyFiveAQ_277, prime_fortyFiveAQ_6810796141, prime_fortyFiveAQ_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272071 : Nat.totient 53202009784627002038011272071 = 53054554534815403587694865760 := by
  rw [← show ((([(397, 1), (3947, 1), (37745866471, 1), (899499665839, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_397, prime_fortyFiveAQ_3947, prime_fortyFiveAQ_37745866471, prime_fortyFiveAQ_899499665839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272072 : Nat.totient 53202009784627002038011272072 = 17520328186295811462437913600 := by
  rw [← show ((([(2, 3), (3, 2), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_83, prime_fortyFiveAQ_1433741, prime_fortyFiveAQ_106163831, prime_fortyFiveAQ_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272073 : Nat.totient 53202009784627002038011272073 = 53202009784627002038011272072 := by
  rw [← show ((([(53202009784627002038011272073, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_53202009784627002038011272073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272074 : Nat.totient 53202009784627002038011272074 = 25882052628047801612940183744 := by
  rw [← show ((([(2, 1), (37, 1), (4183909, 1), (171835974006756638989, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_37, prime_fortyFiveAQ_4183909, prime_fortyFiveAQ_171835974006756638989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272075 : Nat.totient 53202009784627002038011272075 = 28235169641970638323525785600 := by
  rw [← show ((([(3, 1), (5, 2), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_281, prime_fortyFiveAQ_739, prime_fortyFiveAQ_3540386347, prime_fortyFiveAQ_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272076 : Nat.totient 53202009784627002038011272076 = 25200689937465351874283089920 := by
  rw [← show ((([(2, 2), (19, 1), (164881, 1), (230729, 1), (18401009513612249, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_19, prime_fortyFiveAQ_164881, prime_fortyFiveAQ_230729, prime_fortyFiveAQ_18401009513612249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272077 : Nat.totient 53202009784627002038011272077 = 41452639774598746610466753600 := by
  rw [← show ((([(7, 1), (11, 1), (11941, 1), (92349473219, 1), (626559317519, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_7, prime_fortyFiveAQ_11, prime_fortyFiveAQ_11941, prime_fortyFiveAQ_92349473219, prime_fortyFiveAQ_626559317519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272078 : Nat.totient 53202009784627002038011272078 = 16249838054458671858537179136 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (137, 1), (31063, 1), (912772537, 1), (175592882183, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_13, prime_fortyFiveAQ_137, prime_fortyFiveAQ_31063, prime_fortyFiveAQ_912772537, prime_fortyFiveAQ_175592882183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272079 : Nat.totient 53202009784627002038011272079 = 52693195968467619374891767296 := by
  rw [← show ((([(193, 1), (227, 1), (1214352783196617334413989, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_193, prime_fortyFiveAQ_227, prime_fortyFiveAQ_1214352783196617334413989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272080 : Nat.totient 53202009784627002038011272080 = 21279982661105504751925601280 := by
  rw [← show ((([(2, 4), (5, 1), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_25913, prime_fortyFiveAQ_1731666887, prime_fortyFiveAQ_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272081 : Nat.totient 53202009784627002038011272081 = 35404693774098160667398094592 := by
  rw [← show ((([(3, 4), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_569, prime_fortyFiveAQ_37039, prime_fortyFiveAQ_1544987, prime_fortyFiveAQ_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272082 : Nat.totient 53202009784627002038011272082 = 25722633596039770548927081600 := by
  rw [← show ((([(2, 1), (41, 1), (127, 1), (1021, 1), (5003624649089591221003, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_41, prime_fortyFiveAQ_127, prime_fortyFiveAQ_1021, prime_fortyFiveAQ_5003624649089591221003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272083 : Nat.totient 53202009784627002038011272083 = 51937561282227542250437515264 := by
  rw [← show ((([(89, 1), (107, 1), (317, 1), (4877, 1), (3613617964505360969, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_89, prime_fortyFiveAQ_107, prime_fortyFiveAQ_317, prime_fortyFiveAQ_4877, prime_fortyFiveAQ_3613617964505360969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272084 : Nat.totient 53202009784627002038011272084 = 15200574224179143439431792000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (633357259340797643309658001, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_7, prime_fortyFiveAQ_633357259340797643309658001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272085 : Nat.totient 53202009784627002038011272085 = 40057983837836801534502604800 := by
  rw [← show ((([(5, 1), (17, 1), (625905997466200023976603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_17, prime_fortyFiveAQ_625905997466200023976603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272086 : Nat.totient 53202009784627002038011272086 = 25904885950243793478694980096 := by
  rw [← show ((([(2, 1), (43, 1), (337, 1), (66109, 1), (1177149679, 1), (23588884843, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_43, prime_fortyFiveAQ_337, prime_fortyFiveAQ_66109, prime_fortyFiveAQ_1177149679, prime_fortyFiveAQ_23588884843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272087 : Nat.totient 53202009784627002038011272087 = 34155527019444296072192033280 := by
  rw [← show ((([(3, 1), (29, 1), (383, 1), (1056241, 1), (1511635180256161967, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_29, prime_fortyFiveAQ_383, prime_fortyFiveAQ_1056241, prime_fortyFiveAQ_1511635180256161967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272088 : Nat.totient 53202009784627002038011272088 = 24182731720281866334861404160 := by
  rw [← show ((([(2, 3), (11, 1), (8675153813089, 1), (69689633870809, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_11, prime_fortyFiveAQ_8675153813089, prime_fortyFiveAQ_69689633870809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272089 : Nat.totient 53202009784627002038011272089 = 53153775844470665677710536256 := by
  rw [← show ((([(1103, 1), (2237066599, 1), (21561233991609937, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_1103, prime_fortyFiveAQ_2237066599, prime_fortyFiveAQ_21561233991609937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272090 : Nat.totient 53202009784627002038011272090 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_5, prime_fortyFiveAQ_1222615931, prime_fortyFiveAQ_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272091 : Nat.totient 53202009784627002038011272091 = 42089936818557902691593794464 := by
  rw [← show ((([(7, 1), (13, 1), (10627, 1), (55014347432082082067563, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_7, prime_fortyFiveAQ_13, prime_fortyFiveAQ_10627, prime_fortyFiveAQ_55014347432082082067563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272092 : Nat.totient 53202009784627002038011272092 = 25182125642598473336053432320 := by
  rw [← show ((([(2, 2), (23, 1), (97, 1), (2347844113, 1), (2539213503032641, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_23, prime_fortyFiveAQ_97, prime_fortyFiveAQ_2347844113, prime_fortyFiveAQ_2539213503032641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272093 : Nat.totient 53202009784627002038011272093 = 34321592031814983445888665600 := by
  rw [← show ((([(3, 1), (31, 1), (15073, 1), (4979131, 1), (33351053, 1), (228550559, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_31, prime_fortyFiveAQ_15073, prime_fortyFiveAQ_4979131, prime_fortyFiveAQ_33351053, prime_fortyFiveAQ_228550559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272094 : Nat.totient 53202009784627002038011272094 = 26035026064817469082431048000 := by
  rw [← show ((([(2, 1), (47, 1), (565978827496031936574588001, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_47, prime_fortyFiveAQ_565978827496031936574588001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272095 : Nat.totient 53202009784627002038011272095 = 40310498645275335715135272960 := by
  rw [← show ((([(5, 1), (19, 1), (3691, 1), (401987, 1), (377440396466729153, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_5, prime_fortyFiveAQ_19, prime_fortyFiveAQ_3691, prime_fortyFiveAQ_401987, prime_fortyFiveAQ_377440396466729153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272096 : Nat.totient 53202009784627002038011272096 = 17734003259182272770537103104 := by
  rw [← show ((([(2, 5), (3, 1), (7514213933, 1), (73751906302452347, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_3, prime_fortyFiveAQ_7514213933, prime_fortyFiveAQ_73751906302452347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272097 : Nat.totient 53202009784627002038011272097 = 53194599791279543115390009600 := by
  rw [← show ((([(7789, 1), (91813, 1), (260861261, 1), (285188866661, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_7789, prime_fortyFiveAQ_91813, prime_fortyFiveAQ_260861261, prime_fortyFiveAQ_285188866661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272098 : Nat.totient 53202009784627002038011272098 = 22751615415086161752622741344 := by
  rw [← show ((([(2, 1), (7, 2), (463, 1), (61710917413, 1), (19000234857379, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_7, prime_fortyFiveAQ_463, prime_fortyFiveAQ_61710917413, prime_fortyFiveAQ_19000234857379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272099 : Nat.totient 53202009784627002038011272099 = 31789506485568330350201750400 := by
  rw [← show ((([(3, 2), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_3, prime_fortyFiveAQ_11, prime_fortyFiveAQ_71, prime_fortyFiveAQ_26687336297, prime_fortyFiveAQ_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyFiveAQ_53202009784627002038011272100 : Nat.totient 53202009784627002038011272100 = 20987468322320506899928412160 := by
  rw [← show ((([(2, 2), (5, 2), (73, 1), (11953, 1), (339907, 1), (1793775758729587, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627002038011272100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyFiveAQ_2, prime_fortyFiveAQ_5, prime_fortyFiveAQ_73, prime_fortyFiveAQ_11953, prime_fortyFiveAQ_339907, prime_fortyFiveAQ_1793775758729587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyFiveAQ : certifiedKill 1 53202009784627002038011271999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyFiveAQ_53202009784627002038011272000, phi_fortyFiveAQ_53202009784627002038011272001, phi_fortyFiveAQ_53202009784627002038011272002,
    phi_fortyFiveAQ_53202009784627002038011272003, phi_fortyFiveAQ_53202009784627002038011272004, phi_fortyFiveAQ_53202009784627002038011272005,
    phi_fortyFiveAQ_53202009784627002038011272006, phi_fortyFiveAQ_53202009784627002038011272007, phi_fortyFiveAQ_53202009784627002038011272008,
    phi_fortyFiveAQ_53202009784627002038011272009, phi_fortyFiveAQ_53202009784627002038011272010, phi_fortyFiveAQ_53202009784627002038011272011,
    phi_fortyFiveAQ_53202009784627002038011272012, phi_fortyFiveAQ_53202009784627002038011272013, phi_fortyFiveAQ_53202009784627002038011272014,
    phi_fortyFiveAQ_53202009784627002038011272015, phi_fortyFiveAQ_53202009784627002038011272016, phi_fortyFiveAQ_53202009784627002038011272017,
    phi_fortyFiveAQ_53202009784627002038011272018, phi_fortyFiveAQ_53202009784627002038011272019, phi_fortyFiveAQ_53202009784627002038011272020,
    phi_fortyFiveAQ_53202009784627002038011272021, phi_fortyFiveAQ_53202009784627002038011272022, phi_fortyFiveAQ_53202009784627002038011272023,
    phi_fortyFiveAQ_53202009784627002038011272024, phi_fortyFiveAQ_53202009784627002038011272025, phi_fortyFiveAQ_53202009784627002038011272026,
    phi_fortyFiveAQ_53202009784627002038011272027, phi_fortyFiveAQ_53202009784627002038011272028, phi_fortyFiveAQ_53202009784627002038011272029,
    phi_fortyFiveAQ_53202009784627002038011272030, phi_fortyFiveAQ_53202009784627002038011272031, phi_fortyFiveAQ_53202009784627002038011272032,
    phi_fortyFiveAQ_53202009784627002038011272033, phi_fortyFiveAQ_53202009784627002038011272034, phi_fortyFiveAQ_53202009784627002038011272035,
    phi_fortyFiveAQ_53202009784627002038011272036, phi_fortyFiveAQ_53202009784627002038011272037, phi_fortyFiveAQ_53202009784627002038011272038,
    phi_fortyFiveAQ_53202009784627002038011272039, phi_fortyFiveAQ_53202009784627002038011272040, phi_fortyFiveAQ_53202009784627002038011272041,
    phi_fortyFiveAQ_53202009784627002038011272042, phi_fortyFiveAQ_53202009784627002038011272043, phi_fortyFiveAQ_53202009784627002038011272044,
    phi_fortyFiveAQ_53202009784627002038011272045, phi_fortyFiveAQ_53202009784627002038011272046, phi_fortyFiveAQ_53202009784627002038011272047,
    phi_fortyFiveAQ_53202009784627002038011272048, phi_fortyFiveAQ_53202009784627002038011272049, phi_fortyFiveAQ_53202009784627002038011272050,
    phi_fortyFiveAQ_53202009784627002038011272051, phi_fortyFiveAQ_53202009784627002038011272052, phi_fortyFiveAQ_53202009784627002038011272053,
    phi_fortyFiveAQ_53202009784627002038011272054, phi_fortyFiveAQ_53202009784627002038011272055, phi_fortyFiveAQ_53202009784627002038011272056,
    phi_fortyFiveAQ_53202009784627002038011272057, phi_fortyFiveAQ_53202009784627002038011272058, phi_fortyFiveAQ_53202009784627002038011272059,
    phi_fortyFiveAQ_53202009784627002038011272060, phi_fortyFiveAQ_53202009784627002038011272061, phi_fortyFiveAQ_53202009784627002038011272062,
    phi_fortyFiveAQ_53202009784627002038011272063, phi_fortyFiveAQ_53202009784627002038011272064, phi_fortyFiveAQ_53202009784627002038011272065,
    phi_fortyFiveAQ_53202009784627002038011272066, phi_fortyFiveAQ_53202009784627002038011272067, phi_fortyFiveAQ_53202009784627002038011272068,
    phi_fortyFiveAQ_53202009784627002038011272069, phi_fortyFiveAQ_53202009784627002038011272070, phi_fortyFiveAQ_53202009784627002038011272071,
    phi_fortyFiveAQ_53202009784627002038011272072, phi_fortyFiveAQ_53202009784627002038011272073, phi_fortyFiveAQ_53202009784627002038011272074,
    phi_fortyFiveAQ_53202009784627002038011272075, phi_fortyFiveAQ_53202009784627002038011272076, phi_fortyFiveAQ_53202009784627002038011272077,
    phi_fortyFiveAQ_53202009784627002038011272078, phi_fortyFiveAQ_53202009784627002038011272079, phi_fortyFiveAQ_53202009784627002038011272080,
    phi_fortyFiveAQ_53202009784627002038011272081, phi_fortyFiveAQ_53202009784627002038011272082, phi_fortyFiveAQ_53202009784627002038011272083,
    phi_fortyFiveAQ_53202009784627002038011272084, phi_fortyFiveAQ_53202009784627002038011272085, phi_fortyFiveAQ_53202009784627002038011272086,
    phi_fortyFiveAQ_53202009784627002038011272087, phi_fortyFiveAQ_53202009784627002038011272088, phi_fortyFiveAQ_53202009784627002038011272089,
    phi_fortyFiveAQ_53202009784627002038011272090, phi_fortyFiveAQ_53202009784627002038011272091, phi_fortyFiveAQ_53202009784627002038011272092,
    phi_fortyFiveAQ_53202009784627002038011272093, phi_fortyFiveAQ_53202009784627002038011272094, phi_fortyFiveAQ_53202009784627002038011272095,
    phi_fortyFiveAQ_53202009784627002038011272096, phi_fortyFiveAQ_53202009784627002038011272097, phi_fortyFiveAQ_53202009784627002038011272098,
    phi_fortyFiveAQ_53202009784627002038011272099, phi_fortyFiveAQ_53202009784627002038011272100
  ]

end TotientTailPeriodKiller
end Erdos249257
