import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def quintCFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem quintCFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    quintCFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [quintCFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [quintCFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then quintCFastPow a n * quintCFastPow a n * a
        else quintCFastPow a n * quintCFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_quintC_2 : Nat.Prime 2 := by norm_num
private theorem prime_quintC_3 : Nat.Prime 3 := by norm_num
private theorem prime_quintC_5 : Nat.Prime 5 := by norm_num
private theorem prime_quintC_7 : Nat.Prime 7 := by norm_num
private theorem prime_quintC_11 : Nat.Prime 11 := by norm_num
private theorem prime_quintC_13 : Nat.Prime 13 := by norm_num
private theorem prime_quintC_17 : Nat.Prime 17 := by norm_num
private theorem prime_quintC_19 : Nat.Prime 19 := by norm_num
private theorem prime_quintC_23 : Nat.Prime 23 := by norm_num
private theorem prime_quintC_29 : Nat.Prime 29 := by norm_num
private theorem prime_quintC_31 : Nat.Prime 31 := by norm_num
private theorem prime_quintC_37 : Nat.Prime 37 := by norm_num
private theorem prime_quintC_41 : Nat.Prime 41 := by norm_num
private theorem prime_quintC_43 : Nat.Prime 43 := by norm_num
private theorem prime_quintC_47 : Nat.Prime 47 := by norm_num
private theorem prime_quintC_53 : Nat.Prime 53 := by norm_num
private theorem prime_quintC_59 : Nat.Prime 59 := by norm_num
private theorem prime_quintC_61 : Nat.Prime 61 := by norm_num
private theorem prime_quintC_67 : Nat.Prime 67 := by norm_num
private theorem prime_quintC_71 : Nat.Prime 71 := by norm_num
private theorem prime_quintC_73 : Nat.Prime 73 := by norm_num
private theorem prime_quintC_79 : Nat.Prime 79 := by norm_num
private theorem prime_quintC_83 : Nat.Prime 83 := by norm_num
private theorem prime_quintC_89 : Nat.Prime 89 := by norm_num
private theorem prime_quintC_97 : Nat.Prime 97 := by norm_num
private theorem prime_quintC_101 : Nat.Prime 101 := by norm_num
private theorem prime_quintC_103 : Nat.Prime 103 := by norm_num
private theorem prime_quintC_107 : Nat.Prime 107 := by norm_num
private theorem prime_quintC_109 : Nat.Prime 109 := by norm_num
private theorem prime_quintC_113 : Nat.Prime 113 := by norm_num
private theorem prime_quintC_127 : Nat.Prime 127 := by norm_num
private theorem prime_quintC_131 : Nat.Prime 131 := by norm_num
private theorem prime_quintC_137 : Nat.Prime 137 := by norm_num
private theorem prime_quintC_139 : Nat.Prime 139 := by norm_num
private theorem prime_quintC_163 : Nat.Prime 163 := by norm_num
private theorem prime_quintC_167 : Nat.Prime 167 := by norm_num
private theorem prime_quintC_173 : Nat.Prime 173 := by norm_num
private theorem prime_quintC_179 : Nat.Prime 179 := by norm_num
private theorem prime_quintC_181 : Nat.Prime 181 := by norm_num
private theorem prime_quintC_191 : Nat.Prime 191 := by norm_num
private theorem prime_quintC_197 : Nat.Prime 197 := by norm_num
private theorem prime_quintC_211 : Nat.Prime 211 := by norm_num
private theorem prime_quintC_223 : Nat.Prime 223 := by norm_num
private theorem prime_quintC_227 : Nat.Prime 227 := by norm_num
private theorem prime_quintC_233 : Nat.Prime 233 := by norm_num
private theorem prime_quintC_239 : Nat.Prime 239 := by norm_num
private theorem prime_quintC_241 : Nat.Prime 241 := by norm_num
private theorem prime_quintC_251 : Nat.Prime 251 := by norm_num
private theorem prime_quintC_257 : Nat.Prime 257 := by norm_num
private theorem prime_quintC_263 : Nat.Prime 263 := by norm_num
private theorem prime_quintC_269 : Nat.Prime 269 := by norm_num
private theorem prime_quintC_271 : Nat.Prime 271 := by norm_num
private theorem prime_quintC_283 : Nat.Prime 283 := by norm_num
private theorem prime_quintC_307 : Nat.Prime 307 := by norm_num
private theorem prime_quintC_311 : Nat.Prime 311 := by norm_num
private theorem prime_quintC_313 : Nat.Prime 313 := by norm_num
private theorem prime_quintC_331 : Nat.Prime 331 := by norm_num
private theorem prime_quintC_337 : Nat.Prime 337 := by norm_num
private theorem prime_quintC_349 : Nat.Prime 349 := by norm_num
private theorem prime_quintC_367 : Nat.Prime 367 := by norm_num
private theorem prime_quintC_379 : Nat.Prime 379 := by norm_num
private theorem prime_quintC_397 : Nat.Prime 397 := by norm_num
private theorem prime_quintC_401 : Nat.Prime 401 := by norm_num
private theorem prime_quintC_409 : Nat.Prime 409 := by norm_num
private theorem prime_quintC_421 : Nat.Prime 421 := by norm_num
private theorem prime_quintC_431 : Nat.Prime 431 := by norm_num
private theorem prime_quintC_433 : Nat.Prime 433 := by norm_num
private theorem prime_quintC_443 : Nat.Prime 443 := by norm_num
private theorem prime_quintC_449 : Nat.Prime 449 := by norm_num
private theorem prime_quintC_457 : Nat.Prime 457 := by norm_num
private theorem prime_quintC_461 : Nat.Prime 461 := by norm_num
private theorem prime_quintC_487 : Nat.Prime 487 := by norm_num
private theorem prime_quintC_509 : Nat.Prime 509 := by norm_num
private theorem prime_quintC_557 : Nat.Prime 557 := by norm_num
private theorem prime_quintC_569 : Nat.Prime 569 := by norm_num
private theorem prime_quintC_577 : Nat.Prime 577 := by norm_num
private theorem prime_quintC_599 : Nat.Prime 599 := by norm_num
private theorem prime_quintC_613 : Nat.Prime 613 := by norm_num
private theorem prime_quintC_619 : Nat.Prime 619 := by norm_num
private theorem prime_quintC_631 : Nat.Prime 631 := by norm_num
private theorem prime_quintC_643 : Nat.Prime 643 := by norm_num
private theorem prime_quintC_659 : Nat.Prime 659 := by norm_num
private theorem prime_quintC_701 : Nat.Prime 701 := by norm_num
private theorem prime_quintC_733 : Nat.Prime 733 := by norm_num
private theorem prime_quintC_739 : Nat.Prime 739 := by norm_num
private theorem prime_quintC_751 : Nat.Prime 751 := by norm_num
private theorem prime_quintC_761 : Nat.Prime 761 := by norm_num
private theorem prime_quintC_787 : Nat.Prime 787 := by norm_num
private theorem prime_quintC_797 : Nat.Prime 797 := by norm_num
private theorem prime_quintC_829 : Nat.Prime 829 := by norm_num
private theorem prime_quintC_859 : Nat.Prime 859 := by norm_num
private theorem prime_quintC_877 : Nat.Prime 877 := by norm_num
private theorem prime_quintC_947 : Nat.Prime 947 := by norm_num
private theorem prime_quintC_977 : Nat.Prime 977 := by norm_num
private theorem prime_quintC_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_quintC_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_quintC_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_quintC_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_quintC_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_quintC_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_quintC_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_quintC_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_quintC_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_quintC_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_quintC_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_quintC_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_quintC_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_quintC_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_quintC_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_quintC_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_quintC_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_quintC_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_quintC_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_quintC_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_quintC_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_quintC_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_quintC_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_quintC_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_quintC_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_quintC_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_quintC_2389 : Nat.Prime 2389 := by norm_num
private theorem prime_quintC_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_quintC_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_quintC_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_quintC_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_quintC_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_quintC_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_quintC_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_quintC_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_quintC_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_quintC_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_quintC_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_quintC_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_quintC_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_quintC_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_quintC_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_quintC_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_quintC_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_quintC_4597 : Nat.Prime 4597 := by norm_num
private theorem prime_quintC_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_quintC_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_quintC_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_quintC_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_quintC_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_quintC_5591 : Nat.Prime 5591 := by norm_num
private theorem prime_quintC_5651 : Nat.Prime 5651 := by norm_num
private theorem prime_quintC_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_quintC_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_quintC_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_quintC_6317 : Nat.Prime 6317 := by norm_num
private theorem prime_quintC_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_quintC_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_quintC_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_quintC_7253 : Nat.Prime 7253 := by norm_num
private theorem prime_quintC_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_quintC_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_quintC_7927 : Nat.Prime 7927 := by norm_num
private theorem prime_quintC_8221 : Nat.Prime 8221 := by norm_num
private theorem prime_quintC_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_quintC_9433 : Nat.Prime 9433 := by norm_num
private theorem prime_quintC_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_quintC_9623 : Nat.Prime 9623 := by norm_num
private theorem prime_quintC_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_quintC_10453 : Nat.Prime 10453 := by norm_num
private theorem prime_quintC_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_quintC_11261 : Nat.Prime 11261 := by norm_num
private theorem prime_quintC_11903 : Nat.Prime 11903 := by norm_num
private theorem prime_quintC_12379 : Nat.Prime 12379 := by norm_num
private theorem prime_quintC_12433 : Nat.Prime 12433 := by norm_num
private theorem prime_quintC_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_quintC_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_quintC_13297 : Nat.Prime 13297 := by norm_num
private theorem prime_quintC_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_quintC_13757 : Nat.Prime 13757 := by norm_num
private theorem prime_quintC_14923 : Nat.Prime 14923 := by norm_num
private theorem prime_quintC_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_quintC_16649 : Nat.Prime 16649 := by norm_num
private theorem prime_quintC_17239 : Nat.Prime 17239 := by norm_num
private theorem prime_quintC_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_quintC_19037 : Nat.Prime 19037 := by norm_num
private theorem prime_quintC_19213 : Nat.Prime 19213 := by norm_num
private theorem prime_quintC_19889 : Nat.Prime 19889 := by norm_num
private theorem prime_quintC_19993 : Nat.Prime 19993 := by norm_num
private theorem prime_quintC_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_quintC_23509 : Nat.Prime 23509 := by norm_num
private theorem prime_quintC_23827 : Nat.Prime 23827 := by norm_num
private theorem prime_quintC_24517 : Nat.Prime 24517 := by norm_num
private theorem prime_quintC_25943 : Nat.Prime 25943 := by norm_num
private theorem prime_quintC_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_quintC_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_quintC_28927 : Nat.Prime 28927 := by norm_num
private theorem prime_quintC_28961 : Nat.Prime 28961 := by norm_num
private theorem prime_quintC_30427 : Nat.Prime 30427 := by norm_num
private theorem prime_quintC_33809 : Nat.Prime 33809 := by norm_num
private theorem prime_quintC_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_quintC_35023 : Nat.Prime 35023 := by norm_num
private theorem prime_quintC_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_quintC_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_quintC_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_quintC_39551 : Nat.Prime 39551 := by norm_num
private theorem prime_quintC_40577 : Nat.Prime 40577 := by norm_num
private theorem prime_quintC_41609 : Nat.Prime 41609 := by norm_num
private theorem prime_quintC_43517 : Nat.Prime 43517 := by norm_num
private theorem prime_quintC_45119 : Nat.Prime 45119 := by norm_num
private theorem prime_quintC_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_quintC_46681 : Nat.Prime 46681 := by norm_num
private theorem prime_quintC_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_quintC_47837 : Nat.Prime 47837 := by norm_num
private theorem prime_quintC_48383 : Nat.Prime 48383 := by norm_num
private theorem prime_quintC_50753 : Nat.Prime 50753 := by norm_num
private theorem prime_quintC_52541 : Nat.Prime 52541 := by norm_num
private theorem prime_quintC_52579 : Nat.Prime 52579 := by norm_num
private theorem prime_quintC_53407 : Nat.Prime 53407 := by norm_num
private theorem prime_quintC_53813 : Nat.Prime 53813 := by norm_num
private theorem prime_quintC_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_quintC_55001 : Nat.Prime 55001 := by norm_num
private theorem prime_quintC_59393 : Nat.Prime 59393 := by norm_num
private theorem prime_quintC_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_quintC_61927 : Nat.Prime 61927 := by norm_num
private theorem prime_quintC_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_quintC_66301 : Nat.Prime 66301 := by norm_num
private theorem prime_quintC_73819 : Nat.Prime 73819 := by norm_num
private theorem prime_quintC_76831 : Nat.Prime 76831 := by norm_num
private theorem prime_quintC_79777 : Nat.Prime 79777 := by norm_num
private theorem prime_quintC_80567 : Nat.Prime 80567 := by norm_num
private theorem prime_quintC_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_quintC_90191 : Nat.Prime 90191 := by norm_num
private theorem prime_quintC_93287 : Nat.Prime 93287 := by norm_num
private theorem prime_quintC_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_quintC_99611 : Nat.Prime 99611 := by norm_num
private theorem prime_quintC_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_quintC_108923 : Nat.Prime 108923 := by norm_num
private theorem prime_quintC_114671 : Nat.Prime 114671 := by norm_num
private theorem prime_quintC_115319 : Nat.Prime 115319 := by norm_num
private theorem prime_quintC_118687 : Nat.Prime 118687 := by norm_num
private theorem prime_quintC_122167 : Nat.Prime 122167 := by norm_num
private theorem prime_quintC_124459 : Nat.Prime 124459 := by norm_num
private theorem prime_quintC_125497 : Nat.Prime 125497 := by norm_num
private theorem prime_quintC_129439 : Nat.Prime 129439 := by norm_num
private theorem prime_quintC_133559 : Nat.Prime 133559 := by norm_num
private theorem prime_quintC_140197 : Nat.Prime 140197 := by norm_num
private theorem prime_quintC_142151 : Nat.Prime 142151 := by norm_num
private theorem prime_quintC_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_quintC_146009 : Nat.Prime 146009 := by norm_num
private theorem prime_quintC_156139 : Nat.Prime 156139 := by norm_num
private theorem prime_quintC_156521 : Nat.Prime 156521 := by norm_num
private theorem prime_quintC_170447 : Nat.Prime 170447 := by norm_num
private theorem prime_quintC_183707 : Nat.Prime 183707 := by norm_num
private theorem prime_quintC_195341 : Nat.Prime 195341 := by norm_num
private theorem prime_quintC_213949 : Nat.Prime 213949 := by norm_num
private theorem prime_quintC_230189 : Nat.Prime 230189 := by norm_num
private theorem prime_quintC_243707 : Nat.Prime 243707 := by norm_num
private theorem prime_quintC_266957 : Nat.Prime 266957 := by norm_num
private theorem prime_quintC_284957 : Nat.Prime 284957 := by norm_num
private theorem prime_quintC_298031 : Nat.Prime 298031 := by norm_num
private theorem prime_quintC_340037 : Nat.Prime 340037 := by norm_num
private theorem prime_quintC_344873 : Nat.Prime 344873 := by norm_num
private theorem prime_quintC_363563 : Nat.Prime 363563 := by norm_num
private theorem prime_quintC_377711 : Nat.Prime 377711 := by norm_num
private theorem prime_quintC_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_quintC_460793 : Nat.Prime 460793 := by norm_num
private theorem prime_quintC_493133 : Nat.Prime 493133 := by norm_num
private theorem prime_quintC_520957 : Nat.Prime 520957 := by norm_num
private theorem prime_quintC_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_quintC_641057 : Nat.Prime 641057 := by norm_num
private theorem prime_quintC_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_quintC_671633 : Nat.Prime 671633 := by norm_num
private theorem prime_quintC_685493 : Nat.Prime 685493 := by norm_num
private theorem prime_quintC_691531 : Nat.Prime 691531 := by norm_num
private theorem prime_quintC_761681 : Nat.Prime 761681 := by norm_num
private theorem prime_quintC_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_quintC_795791 : Nat.Prime 795791 := by norm_num
private theorem prime_quintC_870853 : Nat.Prime 870853 := by norm_num
private theorem prime_quintC_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_quintC_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_quintC_931751 : Nat.Prime 931751 := by norm_num
private theorem prime_quintC_940369 : Nat.Prime 940369 := by norm_num
private theorem prime_quintC_993323 : Nat.Prime 993323 := by norm_num
private theorem prime_quintC_1033741 : Nat.Prime 1033741 := by norm_num
private theorem prime_quintC_1092397 : Nat.Prime 1092397 := by norm_num
private theorem prime_quintC_1115447 : Nat.Prime 1115447 := by norm_num
private theorem prime_quintC_1159087 : Nat.Prime 1159087 := by norm_num
private theorem prime_quintC_1167211 : Nat.Prime 1167211 := by norm_num
private theorem prime_quintC_1169137 : Nat.Prime 1169137 := by norm_num
private theorem prime_quintC_1319293 : Nat.Prime 1319293 := by norm_num
private theorem prime_quintC_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_quintC_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_quintC_1458659 : Nat.Prime 1458659 := by norm_num
private theorem prime_quintC_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_quintC_1599253 : Nat.Prime 1599253 := by norm_num
private theorem prime_quintC_1726787 : Nat.Prime 1726787 := by norm_num
private theorem prime_quintC_1833389 : Nat.Prime 1833389 := by norm_num
private theorem prime_quintC_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_quintC_1928743 : Nat.Prime 1928743 := by norm_num
private theorem prime_quintC_2098079 : Nat.Prime 2098079 := by norm_num
private theorem prime_quintC_2122619 : Nat.Prime 2122619 := by norm_num
private theorem prime_quintC_2168989 : Nat.Prime 2168989 := by norm_num
private theorem prime_quintC_2182451 : Nat.Prime 2182451 := by norm_num
private theorem prime_quintC_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_quintC_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_quintC_2453597 : Nat.Prime 2453597 := by norm_num
private theorem prime_quintC_2463257 : Nat.Prime 2463257 := by norm_num
private theorem prime_quintC_2507723 : Nat.Prime 2507723 := by norm_num
private theorem prime_quintC_2617129 : Nat.Prime 2617129 := by norm_num
private theorem prime_quintC_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_quintC_3222797 : Nat.Prime 3222797 := by norm_num
private theorem prime_quintC_3421567 : Nat.Prime 3421567 := by norm_num
private theorem prime_quintC_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_quintC_3469177 : Nat.Prime 3469177 := by norm_num
private theorem prime_quintC_3496469 : Nat.Prime 3496469 := by norm_num
private theorem prime_quintC_3523771 : Nat.Prime 3523771 := by norm_num
private theorem prime_quintC_3737029 : Nat.Prime 3737029 := by norm_num
private theorem prime_quintC_3744551 : Nat.Prime 3744551 := by norm_num
private theorem prime_quintC_3976403 : Nat.Prime 3976403 := by norm_num
private theorem prime_quintC_4776769 : Nat.Prime 4776769 := by norm_num
private theorem prime_quintC_5026759 : Nat.Prime 5026759 := by norm_num
private theorem prime_quintC_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_quintC_5075167 : Nat.Prime 5075167 := by norm_num
private theorem prime_quintC_5250043 : Nat.Prime 5250043 := by norm_num
private theorem prime_quintC_5664011 : Nat.Prime 5664011 := by norm_num
private theorem prime_quintC_5987767 : Nat.Prime 5987767 := by norm_num
private theorem prime_quintC_6888173 : Nat.Prime 6888173 := by norm_num
private theorem prime_quintC_6947861 : Nat.Prime 6947861 := by norm_num
private theorem prime_quintC_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_quintC_7294097 : Nat.Prime 7294097 := by norm_num
private theorem prime_quintC_8092963 : Nat.Prime 8092963 := by norm_num
private theorem prime_quintC_8295863 : Nat.Prime 8295863 := by norm_num
private theorem prime_quintC_8837243 : Nat.Prime 8837243 := by norm_num
private theorem prime_quintC_8994889 : Nat.Prime 8994889 := by norm_num
private theorem prime_quintC_9466747 : Nat.Prime 9466747 := by norm_num
private theorem prime_quintC_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_quintC_10379587 : Nat.Prime 10379587 := by norm_num
private theorem prime_quintC_11629967 : Nat.Prime 11629967 := by norm_num
private theorem prime_quintC_12886453 : Nat.Prime 12886453 := by norm_num
private theorem prime_quintC_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_quintC_14598539 : Nat.Prime 14598539 := by norm_num
private theorem prime_quintC_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_quintC_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_quintC_15393431 : Nat.Prime 15393431 := by norm_num
private theorem prime_quintC_15506021 : Nat.Prime 15506021 := by norm_num
private theorem prime_quintC_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_quintC_19230437 : Nat.Prime 19230437 := by norm_num
private theorem prime_quintC_20271367 : Nat.Prime 20271367 := by norm_num
private theorem prime_quintC_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_quintC_22852813 : Nat.Prime 22852813 := by norm_num
private theorem prime_quintC_23622671 : Nat.Prime 23622671 := by norm_num
private theorem prime_quintC_25359827 : Nat.Prime 25359827 := by norm_num
private theorem prime_quintC_29623871 : Nat.Prime 29623871 := by norm_num
private theorem prime_quintC_29728129 : Nat.Prime 29728129 := by norm_num

private theorem prime_quintC_30336529 : Nat.Prime 30336529 := by
  apply lucas_primality 30336529 (7 : ZMod 30336529)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (9433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (9433, 1)] : List FactorBlock).map factorBlockValue).prod) = 30336529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_67
      · exact prime_quintC_9433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 30336529) ^ 15168264 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 30336529) ^ 10112176 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 30336529) ^ 452784 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 30336529) ^ 3216 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_32982869 : Nat.Prime 32982869 := by
  apply lucas_primality 32982869 (2 : ZMod 32982869)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod) = 32982869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_271
      · exact prime_quintC_30427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32982869) ^ 16491434 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 121708 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 1084 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_37866989 : Nat.Prime 37866989 := by
  apply lucas_primality 37866989 (2 : ZMod 37866989)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9466747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9466747, 1)] : List FactorBlock).map factorBlockValue).prod) = 37866989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_9466747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37866989) ^ 18933494 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37866989) ^ 4 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_40376737 : Nat.Prime 40376737 := by
  apply lucas_primality 40376737 (10 : ZMod 40376737)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (140197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (140197, 1)] : List FactorBlock).map factorBlockValue).prod) = 40376737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_140197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 40376737) ^ 20188368 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 40376737) ^ 13458912 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 40376737) ^ 288 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_47684383 : Nat.Prime 47684383 := by
  apply lucas_primality 47684383 (3 : ZMod 47684383)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (233, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (233, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 47684383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_23
      · exact prime_quintC_233
      · exact prime_quintC_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47684383) ^ 23842191 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 15894794 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 2073234 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 204654 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 47684383) ^ 32154 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_51803611 : Nat.Prime 51803611 := by
  apply lucas_primality 51803611 (10 : ZMod 51803611)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1726787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1726787, 1)] : List FactorBlock).map factorBlockValue).prod) = 51803611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_1726787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51803611) ^ 25901805 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 17267870 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 10360722 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 51803611) ^ 30 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_52023863 : Nat.Prime 52023863 := by
  apply lucas_primality 52023863 (5 : ZMod 52023863)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) = 52023863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_19
      · exact prime_quintC_124459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52023863) ^ 26011931 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 4729442 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 2738098 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 418 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_52999753 : Nat.Prime 52999753 := by
  apply lucas_primality 52999753 (5 : ZMod 52999753)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (73, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (73, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 52999753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_13
      · exact prime_quintC_73
      · exact prime_quintC_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52999753) ^ 26499876 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 17666584 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 4076904 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 726024 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52999753) ^ 296088 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_54542561 : Nat.Prime 54542561 := by
  apply lucas_primality 54542561 (3 : ZMod 54542561)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (47, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (47, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) = 54542561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_47
      · exact prime_quintC_7253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54542561) ^ 27271280 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 54542561) ^ 10908512 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 54542561) ^ 1160480 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 54542561) ^ 7520 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_56297287 : Nat.Prime 56297287 := by
  apply lucas_primality 56297287 (3 : ZMod 56297287)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) = 56297287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_67
      · exact prime_quintC_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56297287) ^ 28148643 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 18765762 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 840258 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 1206 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_59247743 : Nat.Prime 59247743 := by
  apply lucas_primality 59247743 (5 : ZMod 59247743)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod) = 59247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_29623871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59247743) ^ 29623871 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 59247743) ^ 2 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_62134759 : Nat.Prime 62134759 := by
  apply lucas_primality 62134759 (11 : ZMod 62134759)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (493133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (493133, 1)] : List FactorBlock).map factorBlockValue).prod) = 62134759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_493133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 62134759) ^ 31067379 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 62134759) ^ 20711586 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 62134759) ^ 8876394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 62134759) ^ 126 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_64144099 : Nat.Prime 64144099 := by
  apply lucas_primality 64144099 (2 : ZMod 64144099)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 64144099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_53
      · exact prime_quintC_71
      · exact prime_quintC_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64144099) ^ 32072049 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 21381366 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 1210266 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 903438 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 67734 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_67426549 : Nat.Prime 67426549 := by
  apply lucas_primality 67426549 (2 : ZMod 67426549)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (114671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (114671, 1)] : List FactorBlock).map factorBlockValue).prod) = 67426549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_114671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67426549) ^ 33713274 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67426549) ^ 22475516 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67426549) ^ 9632364 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67426549) ^ 588 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_72286657 : Nat.Prime 72286657 := by
  apply lucas_primality 72286657 (5 : ZMod 72286657)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (28961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (28961, 1)] : List FactorBlock).map factorBlockValue).prod) = 72286657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_13
      · exact prime_quintC_28961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 72286657) ^ 36143328 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 72286657) ^ 24095552 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 72286657) ^ 5560512 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 72286657) ^ 2496 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_72659089 : Nat.Prime 72659089 := by
  apply lucas_primality 72659089 (7 : ZMod 72659089)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (67, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (67, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 72659089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_67
      · exact prime_quintC_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 72659089) ^ 36329544 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 24219696 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 4274064 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 1084464 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 72659089) ^ 164016 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_75571277 : Nat.Prime 75571277 := by
  apply lucas_primality 75571277 (2 : ZMod 75571277)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (156139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (156139, 1)] : List FactorBlock).map factorBlockValue).prod) = 75571277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_156139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75571277) ^ 37785638 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 75571277) ^ 6870116 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 75571277) ^ 484 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_81085469 : Nat.Prime 81085469 := by
  apply lucas_primality 81085469 (2 : ZMod 81085469)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20271367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20271367, 1)] : List FactorBlock).map factorBlockValue).prod) = 81085469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_20271367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 81085469) ^ 40542734 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 81085469) ^ 4 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_91452329 : Nat.Prime 91452329 := by
  apply lucas_primality 91452329 (3 : ZMod 91452329)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 91452329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_191
      · exact prime_quintC_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91452329) ^ 45726164 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 8313848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 478808 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 16808 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_23
      · exact prime_quintC_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_19
      · exact prime_quintC_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_110782159 : Nat.Prime 110782159 := by
  apply lucas_primality 110782159 (3 : ZMod 110782159)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) = 110782159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_31
      · exact prime_quintC_19213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110782159) ^ 55391079 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 36927386 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 3573618 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 110782159) ^ 5766 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_112046197 : Nat.Prime 112046197 := by
  apply lucas_primality 112046197 (2 : ZMod 112046197)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (751, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (751, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) = 112046197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_751
      · exact prime_quintC_12433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112046197) ^ 56023098 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112046197) ^ 37348732 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112046197) ^ 149196 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112046197) ^ 9012 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_13
      · exact prime_quintC_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_123147449 : Nat.Prime 123147449 := by
  apply lucas_primality 123147449 (3 : ZMod 123147449)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (15393431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (15393431, 1)] : List FactorBlock).map factorBlockValue).prod) = 123147449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_15393431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 123147449) ^ 61573724 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 123147449) ^ 8 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_162618881 : Nat.Prime 162618881 := by
  apply lucas_primality 162618881 (15 : ZMod 162618881)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 162618881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_139
      · exact prime_quintC_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 162618881) ^ 81309440 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 32523776 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 1169920 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 355840 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_169181863 : Nat.Prime 169181863 := by
  apply lucas_primality 169181863 (3 : ZMod 169181863)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (367, 1), (76831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (367, 1), (76831, 1)] : List FactorBlock).map factorBlockValue).prod) = 169181863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_367
      · exact prime_quintC_76831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 169181863) ^ 84590931 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 169181863) ^ 56393954 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 169181863) ^ 460986 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 169181863) ^ 2202 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_178045187 : Nat.Prime 178045187 := by
  apply lucas_primality 178045187 (2 : ZMod 178045187)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (8092963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (8092963, 1)] : List FactorBlock).map factorBlockValue).prod) = 178045187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_8092963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178045187) ^ 89022593 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 178045187) ^ 16185926 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 178045187) ^ 22 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_187518491 : Nat.Prime 187518491 := by
  apply lucas_primality 187518491 (2 : ZMod 187518491)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (787, 1), (23827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (787, 1), (23827, 1)] : List FactorBlock).map factorBlockValue).prod) = 187518491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_787
      · exact prime_quintC_23827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 187518491) ^ 93759245 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 187518491) ^ 37503698 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 187518491) ^ 238270 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 187518491) ^ 7870 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_193301777 : Nat.Prime 193301777 := by
  apply lucas_primality 193301777 (3 : ZMod 193301777)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) = 193301777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_431
      · exact prime_quintC_28031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193301777) ^ 96650888 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 448496 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 6896 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_197212943 : Nat.Prime 197212943 := by
  apply lucas_primality 197212943 (5 : ZMod 197212943)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 197212943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_2069
      · exact prime_quintC_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 197212943) ^ 98606471 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 95318 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 4138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_209339407 : Nat.Prime 209339407 := by
  apply lucas_primality 209339407 (3 : ZMod 209339407)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11629967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11629967, 1)] : List FactorBlock).map factorBlockValue).prod) = 209339407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_11629967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 209339407) ^ 104669703 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 209339407) ^ 69779802 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 209339407) ^ 18 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_29
      · exact prime_quintC_97
      · exact prime_quintC_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_282045737 : Nat.Prime 282045737 := by
  apply lucas_primality 282045737 (3 : ZMod 282045737)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 282045737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_97
      · exact prime_quintC_137
      · exact prime_quintC_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 282045737) ^ 141022868 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 40292248 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2907688 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2058728 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 744184 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_305495041 : Nat.Prime 305495041 := by
  apply lucas_primality 305495041 (7 : ZMod 305495041)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (5, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (5, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) = 305495041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_19889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 305495041) ^ 152747520 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 305495041) ^ 101831680 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 305495041) ^ 61099008 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 305495041) ^ 15360 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_315283291 : Nat.Prime 315283291 := by
  apply lucas_primality 315283291 (7 : ZMod 315283291)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod) = 315283291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_37
      · exact prime_quintC_40577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315283291) ^ 157641645 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 105094430 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 63056658 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 45040470 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 8521170 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 7770 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_336377203 : Nat.Prime 336377203 := by
  apply lucas_primality 336377203 (3 : ZMod 336377203)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (195341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (195341, 1)] : List FactorBlock).map factorBlockValue).prod) = 336377203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_41
      · exact prime_quintC_195341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 336377203) ^ 168188601 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 336377203) ^ 112125734 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 336377203) ^ 48053886 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 336377203) ^ 8204322 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 336377203) ^ 1722 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_359147963 : Nat.Prime 359147963 := by
  apply lucas_primality 359147963 (2 : ZMod 359147963)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod) = 359147963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_47
      · exact prime_quintC_71
      · exact prime_quintC_53813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 359147963) ^ 179573981 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 7641446 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 5058422 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 6674 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_17
      · exact prime_quintC_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_518323783 : Nat.Prime 518323783 := by
  apply lucas_primality 518323783 (5 : ZMod 518323783)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod) = 518323783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_31
      · exact prime_quintC_53
      · exact prime_quintC_52579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 518323783) ^ 259161891 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 172774594 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 16720122 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9779694 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9858 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_522823519 : Nat.Prime 522823519 := by
  apply lucas_primality 522823519 (6 : ZMod 522823519)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) = 522823519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_73
      · exact prime_quintC_18947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522823519) ^ 261411759 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 174274506 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 74689074 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 7161966 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 27594 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_526547381 : Nat.Prime 526547381 := by
  apply lucas_primality 526547381 (3 : ZMod 526547381)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (233, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 526547381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_19
      · exact prime_quintC_233
      · exact prime_quintC_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 526547381) ^ 263273690 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 105309476 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 27713020 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 2259860 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 526547381) ^ 1682260 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_659006597 : Nat.Prime 659006597 := by
  apply lucas_primality 659006597 (2 : ZMod 659006597)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) = 659006597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_257
      · exact prime_quintC_641057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 659006597) ^ 329503298 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 2564228 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 1028 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_757699031 : Nat.Prime 757699031 := by
  apply lucas_primality 757699031 (11 : ZMod 757699031)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (6888173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (6888173, 1)] : List FactorBlock).map factorBlockValue).prod) = 757699031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_11
      · exact prime_quintC_6888173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 757699031) ^ 378849515 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 151539806 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 68881730 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 110 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_854109329 : Nat.Prime 854109329 := by
  apply lucas_primality 854109329 (3 : ZMod 854109329)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (101, 2), (5233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (101, 2), (5233, 1)] : List FactorBlock).map factorBlockValue).prod) = 854109329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_101
      · exact prime_quintC_5233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 854109329) ^ 427054664 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 854109329) ^ 8456528 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 854109329) ^ 163216 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_894938237 : Nat.Prime 894938237 := by
  apply lucas_primality 894938237 (2 : ZMod 894938237)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod) = 894938237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_2777
      · exact prime_quintC_80567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 894938237) ^ 447469118 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 322268 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 11108 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1087747789 : Nat.Prime 1087747789 := by
  apply lucas_primality 1087747789 (2 : ZMod 1087747789)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1087747789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_401
      · exact prime_quintC_13297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1087747789) ^ 543873894 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 362582596 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 63985164 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 2712588 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 81804 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1188346277 : Nat.Prime 1188346277 := by
  apply lucas_primality 1188346277 (2 : ZMod 1188346277)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (22852813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (22852813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188346277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13
      · exact prime_quintC_22852813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1188346277) ^ 594173138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188346277) ^ 91411252 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188346277) ^ 52 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_29
      · exact prime_quintC_113
      · exact prime_quintC_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1385280499 : Nat.Prime 1385280499 := by
  apply lucas_primality 1385280499 (2 : ZMod 1385280499)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1385280499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_32982869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1385280499) ^ 692640249 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 461760166 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 197897214 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 42 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_409
      · exact prime_quintC_443
      · exact prime_quintC_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1814232361 : Nat.Prime 1814232361 := by
  apply lucas_primality 1814232361 (11 : ZMod 1814232361)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (877, 1), (17239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (877, 1), (17239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1814232361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_877
      · exact prime_quintC_17239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1814232361) ^ 907116180 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814232361) ^ 604744120 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814232361) ^ 362846472 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814232361) ^ 2068680 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814232361) ^ 105240 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_89
      · exact prime_quintC_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2010168067 : Nat.Prime 2010168067 := by
  apply lucas_primality 2010168067 (2 : ZMod 2010168067)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (421, 1), (795791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (421, 1), (795791, 1)] : List FactorBlock).map factorBlockValue).prod) = 2010168067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_421
      · exact prime_quintC_795791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2010168067) ^ 1005084033 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2010168067) ^ 670056022 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2010168067) ^ 4774746 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2010168067) ^ 2526 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2206815353 : Nat.Prime 2206815353 := by
  apply lucas_primality 2206815353 (5 : ZMod 2206815353)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (31, 1), (25943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (31, 1), (25943, 1)] : List FactorBlock).map factorBlockValue).prod) = 2206815353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_31
      · exact prime_quintC_25943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2206815353) ^ 1103407676 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2206815353) ^ 315259336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2206815353) ^ 71187592 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2206815353) ^ 85064 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2267800291 : Nat.Prime 2267800291 := by
  apply lucas_primality 2267800291 (26 : ZMod 2267800291)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267800291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_19
      · exact prime_quintC_29
      · exact prime_quintC_47
      · exact prime_quintC_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2267800291) ^ 1133900145 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 755933430 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 453560058 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 323971470 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 119357910 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 78200010 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 48251070 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 16315110 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_61
      · exact prime_quintC_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_3159284287 : Nat.Prime 3159284287 := by
  apply lucas_primality 3159284287 (3 : ZMod 3159284287)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (526547381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (526547381, 1)] : List FactorBlock).map factorBlockValue).prod) = 3159284287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_526547381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3159284287) ^ 1579642143 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159284287) ^ 1053094762 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159284287) ^ 6 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_3665940493 : Nat.Prime 3665940493 := by
  apply lucas_primality 3665940493 (2 : ZMod 3665940493)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (305495041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (305495041, 1)] : List FactorBlock).map factorBlockValue).prod) = 3665940493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_305495041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3665940493) ^ 1832970246 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3665940493) ^ 1221980164 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3665940493) ^ 12 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_4070273261 : Nat.Prime 4070273261 := by
  apply lucas_primality 4070273261 (2 : ZMod 4070273261)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070273261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_97
      · exact prime_quintC_2098079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4070273261) ^ 2035136630 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 814054652 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 41961580 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 1940 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_4476823919 : Nat.Prime 4476823919 := by
  apply lucas_primality 4476823919 (7 : ZMod 4476823919)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (797, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (797, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 4476823919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_71
      · exact prime_quintC_797
      · exact prime_quintC_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4476823919) ^ 2238411959 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4476823919) ^ 639546274 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4476823919) ^ 63053858 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4476823919) ^ 5617094 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4476823919) ^ 792218 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_7795619827 : Nat.Prime 7795619827 := by
  apply lucas_primality 7795619827 (3 : ZMod 7795619827)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (14598539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (14598539, 1)] : List FactorBlock).map factorBlockValue).prod) = 7795619827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_89
      · exact prime_quintC_14598539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7795619827) ^ 3897809913 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 2598539942 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 87591234 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7795619827) ^ 534 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_8015795369 : Nat.Prime 8015795369 := by
  apply lucas_primality 8015795369 (3 : ZMod 8015795369)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (73, 1), (103, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (73, 1), (103, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod) = 8015795369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_73
      · exact prime_quintC_103
      · exact prime_quintC_19037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8015795369) ^ 4007897684 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 1145113624 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 109805416 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 77823256 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8015795369) ^ 421064 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9003352679 : Nat.Prime 9003352679 := by
  apply lucas_primality 9003352679 (19 : ZMod 9003352679)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1039, 1), (1627, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1039, 1), (1627, 1), (2663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9003352679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_1039
      · exact prime_quintC_1627
      · exact prime_quintC_2663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 9003352679) ^ 4501676339 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 8665402 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 5533714 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (19 : ZMod 9003352679) ^ 3380906 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9278485297 : Nat.Prime 9278485297 := by
  apply lucas_primality 9278485297 (5 : ZMod 9278485297)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9278485297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_193301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9278485297) ^ 4639242648 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 3092828432 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 48 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_10040813917 : Nat.Prime 10040813917 := by
  apply lucas_primality 10040813917 (23 : ZMod 10040813917)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3413, 1), (35023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3413, 1), (35023, 1)] : List FactorBlock).map factorBlockValue).prod) = 10040813917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_3413
      · exact prime_quintC_35023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 10040813917) ^ 5020406958 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 3346937972 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 1434401988 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 2941932 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 10040813917) ^ 286692 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_10464329423 : Nat.Prime 10464329423 := by
  apply lucas_primality 10464329423 (5 : ZMod 10464329423)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (51803611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (51803611, 1)] : List FactorBlock).map factorBlockValue).prod) = 10464329423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_101
      · exact prime_quintC_51803611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10464329423) ^ 5232164711 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10464329423) ^ 103607222 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10464329423) ^ 202 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_11266937519 : Nat.Prime 11266937519 := by
  apply lucas_primality 11266937519 (13 : ZMod 11266937519)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (2463257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (2463257, 1)] : List FactorBlock).map factorBlockValue).prod) = 11266937519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_2287
      · exact prime_quintC_2463257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 11266937519) ^ 5633468759 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 11266937519) ^ 4926514 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 11266937519) ^ 4574 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_15383
      · exact prime_quintC_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_12061008403 : Nat.Prime 12061008403 := by
  apply lucas_primality 12061008403 (3 : ZMod 12061008403)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2010168067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2010168067, 1)] : List FactorBlock).map factorBlockValue).prod) = 12061008403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_2010168067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12061008403) ^ 6030504201 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12061008403) ^ 4020336134 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12061008403) ^ 6 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_12103873247 : Nat.Prime 12103873247 := by
  apply lucas_primality 12103873247 (5 : ZMod 12103873247)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (59, 1), (2182451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (59, 1), (2182451, 1)] : List FactorBlock).map factorBlockValue).prod) = 12103873247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_47
      · exact prime_quintC_59
      · exact prime_quintC_2182451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12103873247) ^ 6051936623 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 257529218 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 205150394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12103873247) ^ 5546 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_13445318203 : Nat.Prime 13445318203 := by
  apply lucas_primality 13445318203 (2 : ZMod 13445318203)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (72286657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (72286657, 1)] : List FactorBlock).map factorBlockValue).prod) = 13445318203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_31
      · exact prime_quintC_72286657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13445318203) ^ 6722659101 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 13445318203) ^ 4481772734 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 13445318203) ^ 433719942 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 13445318203) ^ 186 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_23
      · exact prime_quintC_47
      · exact prime_quintC_59
      · exact prime_quintC_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_349
      · exact prime_quintC_619
      · exact prime_quintC_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_15723092741 : Nat.Prime 15723092741 := by
  apply lucas_primality 15723092741 (2 : ZMod 15723092741)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (25359827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (25359827, 1)] : List FactorBlock).map factorBlockValue).prod) = 15723092741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_31
      · exact prime_quintC_25359827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15723092741) ^ 7861546370 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 3144618548 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 507196540 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15723092741) ^ 620 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_15829145149 : Nat.Prime 15829145149 := by
  apply lucas_primality 15829145149 (2 : ZMod 15829145149)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (2381, 1), (10453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (2381, 1), (10453, 1)] : List FactorBlock).map factorBlockValue).prod) = 15829145149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_53
      · exact prime_quintC_2381
      · exact prime_quintC_10453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15829145149) ^ 7914572574 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15829145149) ^ 5276381716 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15829145149) ^ 298663116 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15829145149) ^ 6648108 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15829145149) ^ 1514316 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_16103786791 : Nat.Prime 16103786791 := by
  apply lucas_primality 16103786791 (7 : ZMod 16103786791)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) = 16103786791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_13
      · exact prime_quintC_569
      · exact prime_quintC_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16103786791) ^ 8051893395 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 5367928930 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 3220757358 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 2300540970 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 1238752830 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 28301910 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 10873590 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_18054505621 : Nat.Prime 18054505621 := by
  apply lucas_primality 18054505621 (2 : ZMod 18054505621)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod) = 18054505621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_751
      · exact prime_quintC_133559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18054505621) ^ 9027252810 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 6018168540 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 3610901124 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 24040620 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 135180 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_19648755743 : Nat.Prime 19648755743 := by
  apply lucas_primality 19648755743 (5 : ZMod 19648755743)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (2389, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (2389, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) = 19648755743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_2389
      · exact prime_quintC_53407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19648755743) ^ 9824377871 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19648755743) ^ 2806965106 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19648755743) ^ 1786250522 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19648755743) ^ 8224678 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19648755743) ^ 367906 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_24522826583 : Nat.Prime 24522826583 := by
  apply lucas_primality 24522826583 (5 : ZMod 24522826583)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod) = 24522826583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_31
      · exact prime_quintC_577
      · exact prime_quintC_685493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24522826583) ^ 12261413291 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 791058922 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 42500566 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 35774 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_31
      · exact prime_quintC_71
      · exact prime_quintC_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_27665871067 : Nat.Prime 27665871067 := by
  apply lucas_primality 27665871067 (2 : ZMod 27665871067)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (52999753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (52999753, 1)] : List FactorBlock).map factorBlockValue).prod) = 27665871067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_29
      · exact prime_quintC_52999753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27665871067) ^ 13832935533 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 9221957022 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 953995554 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27665871067) ^ 522 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_17
      · exact prime_quintC_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_31011488803 : Nat.Prime 31011488803 := by
  apply lucas_primality 31011488803 (2 : ZMod 31011488803)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 3), (43, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 3), (43, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31011488803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_37
      · exact prime_quintC_43
      · exact prime_quintC_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31011488803) ^ 15505744401 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31011488803) ^ 10337162934 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31011488803) ^ 4430212686 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31011488803) ^ 838148346 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31011488803) ^ 721197414 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31011488803) ^ 274437954 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_35061805481 : Nat.Prime 35061805481 := by
  apply lucas_primality 35061805481 (3 : ZMod 35061805481)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (67426549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (67426549, 1)] : List FactorBlock).map factorBlockValue).prod) = 35061805481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_13
      · exact prime_quintC_67426549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35061805481) ^ 17530902740 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35061805481) ^ 7012361096 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35061805481) ^ 2697061960 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35061805481) ^ 520 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_38699181337 : Nat.Prime 38699181337 := by
  apply lucas_primality 38699181337 (5 : ZMod 38699181337)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (643, 1), (2507723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (643, 1), (2507723, 1)] : List FactorBlock).map factorBlockValue).prod) = 38699181337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_643
      · exact prime_quintC_2507723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38699181337) ^ 19349590668 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 38699181337) ^ 12899727112 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 38699181337) ^ 60185352 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 38699181337) ^ 15432 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_48138041533 : Nat.Prime 48138041533 := by
  apply lucas_primality 48138041533 (2 : ZMod 48138041533)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (83, 1), (1093, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (83, 1), (1093, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 48138041533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_83
      · exact prime_quintC_1093
      · exact prime_quintC_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48138041533) ^ 24069020766 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48138041533) ^ 16046013844 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48138041533) ^ 6876863076 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48138041533) ^ 579976404 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48138041533) ^ 44042124 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48138041533) ^ 7620396 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_71172712477 : Nat.Prime 71172712477 := by
  apply lucas_primality 71172712477 (2 : ZMod 71172712477)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) = 71172712477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_659006597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71172712477) ^ 35586356238 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 23724237492 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 108 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_84575179597 : Nat.Prime 84575179597 := by
  apply lucas_primality 84575179597 (2 : ZMod 84575179597)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (72659089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (72659089, 1)] : List FactorBlock).map factorBlockValue).prod) = 84575179597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_97
      · exact prime_quintC_72659089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84575179597) ^ 42287589798 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 28191726532 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 871909068 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 84575179597) ^ 1164 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_119438318393 : Nat.Prime 119438318393 := by
  apply lucas_primality 119438318393 (3 : ZMod 119438318393)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (173, 1), (1092397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (173, 1), (1092397, 1)] : List FactorBlock).map factorBlockValue).prod) = 119438318393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_79
      · exact prime_quintC_173
      · exact prime_quintC_1092397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119438318393) ^ 59719159196 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 119438318393) ^ 1511877448 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 119438318393) ^ 690394904 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 119438318393) ^ 109336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_121827752369 : Nat.Prime 121827752369 := by
  apply lucas_primality 121827752369 (3 : ZMod 121827752369)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) = 121827752369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_1087747789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 121827752369) ^ 60913876184 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 17403964624 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 112 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_134304717571 : Nat.Prime 134304717571 := by
  apply lucas_primality 134304717571 (12 : ZMod 134304717571)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4476823919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4476823919, 1)] : List FactorBlock).map factorBlockValue).prod) = 134304717571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_4476823919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 134304717571) ^ 67152358785 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (12 : ZMod 134304717571) ^ 44768239190 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (12 : ZMod 134304717571) ^ 26860943514 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (12 : ZMod 134304717571) ^ 30 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_137253738091 : Nat.Prime 137253738091 := by
  apply lucas_primality 137253738091 (10 : ZMod 137253738091)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (3889, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (3889, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) = 137253738091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_23
      · exact prime_quintC_3889
      · exact prime_quintC_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 137253738091) ^ 68626869045 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 45751246030 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 27450747618 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 19607676870 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 5967553830 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 35292810 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 137253738091) ^ 18783870 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_158291451491 : Nat.Prime 158291451491 := by
  apply lucas_primality 158291451491 (2 : ZMod 158291451491)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15829145149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15829145149, 1)] : List FactorBlock).map factorBlockValue).prod) = 158291451491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_15829145149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158291451491) ^ 79145725745 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158291451491) ^ 31658290298 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158291451491) ^ 10 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_199731886537 : Nat.Prime 199731886537 := by
  apply lucas_primality 199731886537 (10 : ZMod 199731886537)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (91452329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (91452329, 1)] : List FactorBlock).map factorBlockValue).prod) = 199731886537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_13
      · exact prime_quintC_91452329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 199731886537) ^ 99865943268 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 66577295512 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 28533126648 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 15363991272 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 2184 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_208255577671 : Nat.Prime 208255577671 := by
  apply lucas_primality 208255577671 (7 : ZMod 208255577671)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (107, 1), (109, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (107, 1), (109, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 208255577671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_107
      · exact prime_quintC_109
      · exact prime_quintC_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 208255577671) ^ 104127788835 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 69418525890 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 41651115534 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 29750796810 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 1946313810 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 1910601630 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 51433830 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_343861521697 : Nat.Prime 343861521697 := by
  apply lucas_primality 343861521697 (10 : ZMod 343861521697)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (11, 1), (15506021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (11, 1), (15506021, 1)] : List FactorBlock).map factorBlockValue).prod) = 343861521697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_15506021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 343861521697) ^ 171930760848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 343861521697) ^ 114620507232 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 343861521697) ^ 49123074528 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 343861521697) ^ 31260138336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 343861521697) ^ 22176 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_400062744481 : Nat.Prime 400062744481 := by
  apply lucas_primality 400062744481 (23 : ZMod 400062744481)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod) = 400062744481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_19
      · exact prime_quintC_131
      · exact prime_quintC_47837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 400062744481) ^ 200031372240 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 133354248160 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 80012548896 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 57151820640 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 21055933920 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 3053914080 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 8363040 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_400261864237 : Nat.Prime 400261864237 := by
  apply lucas_primality 400261864237 (5 : ZMod 400261864237)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1759, 1), (1458659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1759, 1), (1458659, 1)] : List FactorBlock).map factorBlockValue).prod) = 400261864237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_13
      · exact prime_quintC_1759
      · exact prime_quintC_1458659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 400261864237) ^ 200130932118 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 400261864237) ^ 133420621412 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 400261864237) ^ 30789374172 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 400261864237) ^ 227550804 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 400261864237) ^ 274404 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_404640326119 : Nat.Prime 404640326119 := by
  apply lucas_primality 404640326119 (3 : ZMod 404640326119)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (73, 1), (7927, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (73, 1), (7927, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod) = 404640326119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_73
      · exact prime_quintC_7927
      · exact prime_quintC_16649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 404640326119) ^ 202320163059 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 404640326119) ^ 134880108706 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 404640326119) ^ 57805760874 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 404640326119) ^ 5543018166 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 404640326119) ^ 51045834 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 404640326119) ^ 24304182 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_417309099223 : Nat.Prime 417309099223 := by
  apply lucas_primality 417309099223 (3 : ZMod 417309099223)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (3793, 1), (52541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (3793, 1), (52541, 1)] : List FactorBlock).map factorBlockValue).prod) = 417309099223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_349
      · exact prime_quintC_3793
      · exact prime_quintC_52541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 417309099223) ^ 208654549611 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 139103033074 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 1195728078 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 110020854 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 417309099223) ^ 7942542 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_17
      · exact prime_quintC_397
      · exact prime_quintC_2531
      · exact prime_quintC_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_473509638713 : Nat.Prime 473509638713 := by
  apply lucas_primality 473509638713 (3 : ZMod 473509638713)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (181, 1), (29728129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (181, 1), (29728129, 1)] : List FactorBlock).map factorBlockValue).prod) = 473509638713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_181
      · exact prime_quintC_29728129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 473509638713) ^ 236754819356 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 473509638713) ^ 43046330792 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 473509638713) ^ 2616075352 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 473509638713) ^ 15928 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_504627554647 : Nat.Prime 504627554647 := by
  apply lucas_primality 504627554647 (3 : ZMod 504627554647)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (757699031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (757699031, 1)] : List FactorBlock).map factorBlockValue).prod) = 504627554647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_37
      · exact prime_quintC_757699031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 504627554647) ^ 252313777323 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 168209184882 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 13638582558 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 666 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_587043060839 : Nat.Prime 587043060839 := by
  apply lucas_primality 587043060839 (7 : ZMod 587043060839)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (1188346277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (1188346277, 1)] : List FactorBlock).map factorBlockValue).prod) = 587043060839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13
      · exact prime_quintC_19
      · exact prime_quintC_1188346277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 587043060839) ^ 293521530419 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 45157158526 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 30897003202 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 587043060839) ^ 494 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_29
      · exact prime_quintC_34361
      · exact prime_quintC_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_950931947653 : Nat.Prime 950931947653 := by
  apply lucas_primality 950931947653 (2 : ZMod 950931947653)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79777, 1), (993323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79777, 1), (993323, 1)] : List FactorBlock).map factorBlockValue).prod) = 950931947653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_79777
      · exact prime_quintC_993323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 950931947653) ^ 475465973826 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 950931947653) ^ 316977315884 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 950931947653) ^ 11919876 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 950931947653) ^ 957324 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_955333581581 : Nat.Prime 955333581581 := by
  apply lucas_primality 955333581581 (10 : ZMod 955333581581)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod) = 955333581581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_19
      · exact prime_quintC_359147963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 955333581581) ^ 477666790790 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 191066716316 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 136476225940 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 50280714820 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 2660 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1177151406131 : Nat.Prime 1177151406131 := by
  apply lucas_primality 1177151406131 (2 : ZMod 1177151406131)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2969, 1), (5664011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2969, 1), (5664011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1177151406131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_2969
      · exact prime_quintC_5664011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1177151406131) ^ 588575703065 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177151406131) ^ 235430281226 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177151406131) ^ 168164486590 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177151406131) ^ 396480770 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177151406131) ^ 207830 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1241877643471 : Nat.Prime 1241877643471 := by
  apply lucas_primality 1241877643471 (11 : ZMod 1241877643471)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (179, 1), (631, 1), (122167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (179, 1), (631, 1), (122167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1241877643471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_179
      · exact prime_quintC_631
      · exact prime_quintC_122167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1241877643471) ^ 620938821735 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1241877643471) ^ 413959214490 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1241877643471) ^ 248375528694 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1241877643471) ^ 6937863930 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1241877643471) ^ 1968110370 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1241877643471) ^ 10165410 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1372447766351 : Nat.Prime 1372447766351 := by
  apply lucas_primality 1372447766351 (7 : ZMod 1372447766351)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1372447766351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_17
      · exact prime_quintC_9473
      · exact prime_quintC_170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1372447766351) ^ 686223883175 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 274489553270 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 80732221550 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 144879950 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 8052050 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_397
      · exact prime_quintC_977
      · exact prime_quintC_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_35279
      · exact prime_quintC_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1920997335277 : Nat.Prime 1920997335277 := by
  apply lucas_primality 1920997335277 (2 : ZMod 1920997335277)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (109, 1), (131, 1), (3737029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (109, 1), (131, 1), (3737029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1920997335277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_109
      · exact prime_quintC_131
      · exact prime_quintC_3737029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1920997335277) ^ 960498667638 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1920997335277) ^ 640332445092 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1920997335277) ^ 17623828764 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1920997335277) ^ 14664101796 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1920997335277) ^ 514044 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1981109685367 : Nat.Prime 1981109685367 := by
  apply lucas_primality 1981109685367 (3 : ZMod 1981109685367)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (15723092741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (15723092741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1981109685367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_15723092741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1981109685367) ^ 990554842683 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 660369895122 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 283015669338 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1981109685367) ^ 126 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2214349910519 : Nat.Prime 2214349910519 := by
  apply lucas_primality 2214349910519 (13 : ZMod 2214349910519)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (48138041533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (48138041533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2214349910519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_23
      · exact prime_quintC_48138041533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 2214349910519) ^ 1107174955259 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 2214349910519) ^ 96276083066 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 2214349910519) ^ 46 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2231902209599 : Nat.Prime 2231902209599 := by
  apply lucas_primality 2231902209599 (19 : ZMod 2231902209599)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2231902209599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_2153
      · exact prime_quintC_518323783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 2231902209599) ^ 1115951104799 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 1036647566 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 4306 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2499066932053 : Nat.Prime 2499066932053 := by
  apply lucas_primality 2499066932053 (2 : ZMod 2499066932053)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (208255577671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (208255577671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2499066932053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_208255577671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2499066932053) ^ 1249533466026 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499066932053) ^ 833022310684 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499066932053) ^ 12 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_761
      · exact prime_quintC_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_381559
      · exact prime_quintC_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_7924438741469 : Nat.Prime 7924438741469 := by
  apply lucas_primality 7924438741469 (2 : ZMod 7924438741469)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1981109685367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1981109685367, 1)] : List FactorBlock).map factorBlockValue).prod) = 7924438741469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_1981109685367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7924438741469) ^ 3962219370734 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7924438741469) ^ 4 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_8214816212531 : Nat.Prime 8214816212531 := by
  apply lucas_primality 8214816212531 (2 : ZMod 8214816212531)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (5591, 1), (298031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (5591, 1), (298031, 1)] : List FactorBlock).map factorBlockValue).prod) = 8214816212531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_17
      · exact prime_quintC_29
      · exact prime_quintC_5591
      · exact prime_quintC_298031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8214816212531) ^ 4107408106265 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8214816212531) ^ 1642963242506 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8214816212531) ^ 483224483090 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8214816212531) ^ 283269524570 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8214816212531) ^ 1469292830 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8214816212531) ^ 27563630 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_8252676520729 : Nat.Prime 8252676520729 := by
  apply lucas_primality 8252676520729 (37 : ZMod 8252676520729)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (343861521697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (343861521697, 1)] : List FactorBlock).map factorBlockValue).prod) = 8252676520729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_343861521697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 8252676520729) ^ 4126338260364 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (37 : ZMod 8252676520729) ^ 2750892173576 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (37 : ZMod 8252676520729) ^ 24 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_8350133606891 : Nat.Prime 8350133606891 := by
  apply lucas_primality 8350133606891 (10 : ZMod 8350133606891)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (71, 1), (241, 1), (307, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (71, 1), (241, 1), (307, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) = 8350133606891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_41
      · exact prime_quintC_71
      · exact prime_quintC_241
      · exact prime_quintC_307
      · exact prime_quintC_3877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8350133606891) ^ 4175066803445 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 1670026721378 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 203661795290 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 117607515590 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 34647857290 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 27199132270 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 8350133606891) ^ 2153761570 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_13
      · exact prime_quintC_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_20919126693301 : Nat.Prime 20919126693301 := by
  apply lucas_primality 20919126693301 (2 : ZMod 20919126693301)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (13757, 1), (460793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (13757, 1), (460793, 1)] : List FactorBlock).map factorBlockValue).prod) = 20919126693301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_11
      · exact prime_quintC_13757
      · exact prime_quintC_460793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20919126693301) ^ 10459563346650 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20919126693301) ^ 6973042231100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20919126693301) ^ 4183825338660 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20919126693301) ^ 1901738790300 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20919126693301) ^ 1520616900 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20919126693301) ^ 45398100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_22575350790673 : Nat.Prime 22575350790673 := by
  apply lucas_primality 22575350790673 (10 : ZMod 22575350790673)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (27665871067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (27665871067, 1)] : List FactorBlock).map factorBlockValue).prod) = 22575350790673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_27665871067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 22575350790673) ^ 11287675395336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 7525116930224 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 1327961811216 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 22575350790673) ^ 816 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_23967228153311 : Nat.Prime 23967228153311 := by
  apply lucas_primality 23967228153311 (7 : ZMod 23967228153311)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (8015795369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (8015795369, 1)] : List FactorBlock).map factorBlockValue).prod) = 23967228153311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_13
      · exact prime_quintC_23
      · exact prime_quintC_8015795369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23967228153311) ^ 11983614076655 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 4793445630662 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 1843632934870 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 1042053397970 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23967228153311) ^ 2990 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_23
      · exact prime_quintC_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_47934456306623 : Nat.Prime 47934456306623 := by
  apply lucas_primality 47934456306623 (5 : ZMod 47934456306623)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23967228153311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23967228153311, 1)] : List FactorBlock).map factorBlockValue).prod) = 47934456306623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_23967228153311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 47934456306623) ^ 23967228153311 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 47934456306623) ^ 2 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_95868912613247 : Nat.Prime 95868912613247 := by
  apply lucas_primality 95868912613247 (5 : ZMod 95868912613247)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47934456306623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47934456306623, 1)] : List FactorBlock).map factorBlockValue).prod) = 95868912613247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_47934456306623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 95868912613247) ^ 47934456306623 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 95868912613247) ^ 2 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_100273503081211 : Nat.Prime 100273503081211 := by
  apply lucas_primality 100273503081211 (2 : ZMod 100273503081211)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (1297, 1), (112046197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (1297, 1), (112046197, 1)] : List FactorBlock).map factorBlockValue).prod) = 100273503081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_23
      · exact prime_quintC_1297
      · exact prime_quintC_112046197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100273503081211) ^ 50136751540605 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 100273503081211) ^ 33424501027070 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 100273503081211) ^ 20054700616242 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 100273503081211) ^ 4359717525270 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 100273503081211) ^ 77311875930 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 100273503081211) ^ 894930 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_129951480466757 : Nat.Prime 129951480466757 := by
  apply lucas_primality 129951480466757 (3 : ZMod 129951480466757)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2499066932053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2499066932053, 1)] : List FactorBlock).map factorBlockValue).prod) = 129951480466757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13
      · exact prime_quintC_2499066932053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129951480466757) ^ 64975740233378 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 129951480466757) ^ 9996267728212 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 129951480466757) ^ 52 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_148978605984457 : Nat.Prime 148978605984457 := by
  apply lucas_primality 148978605984457 (10 : ZMod 148978605984457)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod) = 148978605984457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_4481
      · exact prime_quintC_1385280499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 148978605984457) ^ 74489302992228 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 49659535328152 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 33246731976 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 107544 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_1163
      · exact prime_quintC_1663
      · exact prime_quintC_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_334706027092817 : Nat.Prime 334706027092817 := by
  apply lucas_primality 334706027092817 (3 : ZMod 334706027092817)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20919126693301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20919126693301, 1)] : List FactorBlock).map factorBlockValue).prod) = 334706027092817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_20919126693301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 334706027092817) ^ 167353013546408 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 334706027092817) ^ 16 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_369954349991773 : Nat.Prime 369954349991773 := by
  apply lucas_primality 369954349991773 (5 : ZMod 369954349991773)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (4483, 1), (75571277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (4483, 1), (75571277, 1)] : List FactorBlock).map factorBlockValue).prod) = 369954349991773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_13
      · exact prime_quintC_4483
      · exact prime_quintC_75571277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 369954349991773) ^ 184977174995886 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 123318116663924 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 52850621427396 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 28458026922444 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 82523834484 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 4895436 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_388383853927687 : Nat.Prime 388383853927687 := by
  apply lucas_primality 388383853927687 (3 : ZMod 388383853927687)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (363563, 1), (178045187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (363563, 1), (178045187, 1)] : List FactorBlock).map factorBlockValue).prod) = 388383853927687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_363563
      · exact prime_quintC_178045187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 388383853927687) ^ 194191926963843 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 129461284642562 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 1068271122 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 388383853927687) ^ 2181378 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_67
      · exact prime_quintC_28807
      · exact prime_quintC_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_493853323129583 : Nat.Prime 493853323129583 := by
  apply lucas_primality 493853323129583 (5 : ZMod 493853323129583)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3976403, 1), (4776769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3976403, 1), (4776769, 1)] : List FactorBlock).map factorBlockValue).prod) = 493853323129583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13
      · exact prime_quintC_3976403
      · exact prime_quintC_4776769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 493853323129583) ^ 246926661564791 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 37988717163814 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 124195994 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 493853323129583) ^ 103386478 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_518378746886659 : Nat.Prime 518378746886659 := by
  apply lucas_primality 518378746886659 (3 : ZMod 518378746886659)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (12379, 1), (110782159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (12379, 1), (110782159, 1)] : List FactorBlock).map factorBlockValue).prod) = 518378746886659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_12379
      · exact prime_quintC_110782159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 518378746886659) ^ 259189373443329 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 172792915628886 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 74054106698094 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 41875656102 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 518378746886659) ^ 4679262 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_576001613200633 : Nat.Prime 576001613200633 := by
  apply lucas_primality 576001613200633 (5 : ZMod 576001613200633)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) = 576001613200633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_197
      · exact prime_quintC_121827752369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 576001613200633) ^ 288000806600316 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 192000537733544 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 2923866056856 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 4728 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_47
      · exact prime_quintC_71
      · exact prime_quintC_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1463629363053257 : Nat.Prime 1463629363053257 := by
  apply lucas_primality 1463629363053257 (3 : ZMod 1463629363053257)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (137, 1), (10040813917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (137, 1), (10040813917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1463629363053257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_19
      · exact prime_quintC_137
      · exact prime_quintC_10040813917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1463629363053257) ^ 731814681526628 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 209089909007608 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 77033124371224 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 10683426007688 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1463629363053257) ^ 145768 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1472991480313183 : Nat.Prime 1472991480313183 := by
  apply lucas_primality 1472991480313183 (5 : ZMod 1472991480313183)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472991480313183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_156521
      · exact prime_quintC_522823519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1472991480313183) ^ 736495740156591 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 490997160104394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 9410823342 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 2817378 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_41
      · exact prime_quintC_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2246336628673273 : Nat.Prime 2246336628673273 := by
  apply lucas_primality 2246336628673273 (5 : ZMod 2246336628673273)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (1783, 1), (2251, 1), (213949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (1783, 1), (2251, 1), (213949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246336628673273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_109
      · exact prime_quintC_1783
      · exact prime_quintC_2251
      · exact prime_quintC_213949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2246336628673273) ^ 1123168314336636 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2246336628673273) ^ 748778876224424 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2246336628673273) ^ 20608592923608 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2246336628673273) ^ 1259863504584 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2246336628673273) ^ 997928311272 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2246336628673273) ^ 10499402328 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2743295750628703 : Nat.Prime 2743295750628703 := by
  apply lucas_primality 2743295750628703 (5 : ZMod 2743295750628703)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2743295750628703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_2531
      · exact prime_quintC_3049
      · exact prime_quintC_59247743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2743295750628703) ^ 1371647875314351 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 914431916876234 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 1083878210442 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 899736225198 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 46302114 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_3008297016953401 : Nat.Prime 3008297016953401 := by
  apply lucas_primality 3008297016953401 (17 : ZMod 3008297016953401)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (659, 1), (733, 1), (10379587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (659, 1), (733, 1), (10379587, 1)] : List FactorBlock).map factorBlockValue).prod) = 3008297016953401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_659
      · exact prime_quintC_733
      · exact prime_quintC_10379587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3008297016953401) ^ 1504148508476700 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 1002765672317800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 601659403390680 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 4564942362600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 4104088699800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3008297016953401) ^ 289828200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_4211487129410863 : Nat.Prime 4211487129410863 := by
  apply lucas_primality 4211487129410863 (5 : ZMod 4211487129410863)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (100273503081211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (100273503081211, 1)] : List FactorBlock).map factorBlockValue).prod) = 4211487129410863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_100273503081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4211487129410863) ^ 2105743564705431 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4211487129410863) ^ 1403829043136954 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4211487129410863) ^ 601641018487266 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4211487129410863) ^ 42 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9253358886649121 : Nat.Prime 9253358886649121 := by
  apply lucas_primality 9253358886649121 (3 : ZMod 9253358886649121)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (23, 1), (139, 1), (4831, 1), (3744551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (23, 1), (139, 1), (4831, 1), (3744551, 1)] : List FactorBlock).map factorBlockValue).prod) = 9253358886649121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_23
      · exact prime_quintC_139
      · exact prime_quintC_4831
      · exact prime_quintC_3744551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9253358886649121) ^ 4626679443324560 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9253358886649121) ^ 1850671777329824 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9253358886649121) ^ 402319951593440 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9253358886649121) ^ 66570927242080 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9253358886649121) ^ 1915412727520 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9253358886649121) ^ 2471153120 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9271321778674247 : Nat.Prime 9271321778674247 := by
  apply lucas_primality 9271321778674247 (5 : ZMod 9271321778674247)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9271321778674247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_31
      · exact prime_quintC_67
      · exact prime_quintC_2231902209599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9271321778674247) ^ 4635660889337123 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 299074896086266 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 138377936995138 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 4154 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9438995739323077 : Nat.Prime 9438995739323077 := by
  apply lucas_primality 9438995739323077 (2 : ZMod 9438995739323077)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (739, 1), (1907, 1), (9013, 1), (61927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (739, 1), (1907, 1), (9013, 1), (61927, 1)] : List FactorBlock).map factorBlockValue).prod) = 9438995739323077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_739
      · exact prime_quintC_1907
      · exact prime_quintC_9013
      · exact prime_quintC_61927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9438995739323077) ^ 4719497869661538 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9438995739323077) ^ 3146331913107692 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9438995739323077) ^ 12772659999084 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9438995739323077) ^ 4949656916268 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9438995739323077) ^ 1047264588852 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9438995739323077) ^ 152421330588 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_67
      · exact prime_quintC_97
      · exact prime_quintC_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_13528531400913343 : Nat.Prime 13528531400913343 := by
  apply lucas_primality 13528531400913343 (3 : ZMod 13528531400913343)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (631, 1), (10243, 1), (3523771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (631, 1), (10243, 1), (3523771, 1)] : List FactorBlock).map factorBlockValue).prod) = 13528531400913343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_11
      · exact prime_quintC_631
      · exact prime_quintC_10243
      · exact prime_quintC_3523771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13528531400913343) ^ 6764265700456671 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 4509510466971114 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 1229866490992122 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 21439827893682 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 1320758703594 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13528531400913343) ^ 3839219802 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_14484700483141487 : Nat.Prime 14484700483141487 := by
  apply lucas_primality 14484700483141487 (5 : ZMod 14484700483141487)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (73, 1), (587043060839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (73, 1), (587043060839, 1)] : List FactorBlock).map factorBlockValue).prod) = 14484700483141487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13
      · exact prime_quintC_73
      · exact prime_quintC_587043060839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14484700483141487) ^ 7242350241570743 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 1114207729472422 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 198420554563582 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14484700483141487) ^ 24674 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_14768667586612591 : Nat.Prime 14768667586612591 := by
  apply lucas_primality 14768667586612591 (7 : ZMod 14768667586612591)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (23509, 1), (37866989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (23509, 1), (37866989, 1)] : List FactorBlock).map factorBlockValue).prod) = 14768667586612591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_79
      · exact prime_quintC_23509
      · exact prime_quintC_37866989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14768667586612591) ^ 7384333793306295 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 4922889195537530 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 2953733517322518 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 2109809655230370 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 186945159324210 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 628213347510 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14768667586612591) ^ 390014310 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_23866740497948269 : Nat.Prime 23866740497948269 := by
  apply lucas_primality 23866740497948269 (2 : ZMod 23866740497948269)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (8252676520729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (8252676520729, 1)] : List FactorBlock).map factorBlockValue).prod) = 23866740497948269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_241
      · exact prime_quintC_8252676520729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23866740497948269) ^ 11933370248974134 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23866740497948269) ^ 7955580165982756 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23866740497948269) ^ 99032118248748 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23866740497948269) ^ 2892 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_19
      · exact prime_quintC_656951
      · exact prime_quintC_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_32801190655096067 : Nat.Prime 32801190655096067 := by
  apply lucas_primality 32801190655096067 (2 : ZMod 32801190655096067)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (334706027092817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (334706027092817, 1)] : List FactorBlock).map factorBlockValue).prod) = 32801190655096067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_334706027092817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32801190655096067) ^ 16400595327548033 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32801190655096067) ^ 4685884379299438 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32801190655096067) ^ 98 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_33531643827487633 : Nat.Prime 33531643827487633 := by
  apply lucas_primality 33531643827487633 (15 : ZMod 33531643827487633)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) = 33531643827487633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_509
      · exact prime_quintC_1372447766351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 33531643827487633) ^ 16765821913743816 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 11177214609162544 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 65877492784848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 24432 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_34129332890315933 : Nat.Prime 34129332890315933 := by
  apply lucas_primality 34129332890315933 (2 : ZMod 34129332890315933)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (95868912613247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (95868912613247, 1)] : List FactorBlock).map factorBlockValue).prod) = 34129332890315933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_89
      · exact prime_quintC_95868912613247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34129332890315933) ^ 17064666445157966 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34129332890315933) ^ 383475650452988 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34129332890315933) ^ 356 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_38130284867107679 : Nat.Prime 38130284867107679 := by
  apply lucas_primality 38130284867107679 (11 : ZMod 38130284867107679)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (181, 1), (520957, 1), (931751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (181, 1), (520957, 1), (931751, 1)] : List FactorBlock).map factorBlockValue).prod) = 38130284867107679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7
      · exact prime_quintC_31
      · exact prime_quintC_181
      · exact prime_quintC_520957
      · exact prime_quintC_931751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 38130284867107679) ^ 19065142433553839 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 38130284867107679) ^ 5447183552443954 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 38130284867107679) ^ 1230009189261538 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 38130284867107679) ^ 210664557276838 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 38130284867107679) ^ 73192768054 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 38130284867107679) ^ 40923256178 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_44014346833268107 : Nat.Prime 44014346833268107 := by
  apply lucas_primality 44014346833268107 (5 : ZMod 44014346833268107)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6043, 1), (404640326119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6043, 1), (404640326119, 1)] : List FactorBlock).map factorBlockValue).prod) = 44014346833268107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_6043
      · exact prime_quintC_404640326119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44014346833268107) ^ 22007173416634053 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 44014346833268107) ^ 14671448944422702 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 44014346833268107) ^ 7283525870142 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 44014346833268107) ^ 108774 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_76260569734215359 : Nat.Prime 76260569734215359 := by
  apply lucas_primality 76260569734215359 (11 : ZMod 76260569734215359)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (38130284867107679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (38130284867107679, 1)] : List FactorBlock).map factorBlockValue).prod) = 76260569734215359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_38130284867107679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 76260569734215359) ^ 38130284867107679 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76260569734215359) ^ 2 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_13421
      · exact prime_quintC_99611
      · exact prime_quintC_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_284004322561366753 : Nat.Prime 284004322561366753 := by
  apply lucas_primality 284004322561366753 (5 : ZMod 284004322561366753)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod) = 284004322561366753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_183707
      · exact prime_quintC_16103786791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284004322561366753) ^ 142002161280683376 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 94668107520455584 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 1545963531936 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 17635872 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_5037757
      · exact prime_quintC_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_29
      · exact prime_quintC_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_61717
      · exact prime_quintC_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_941217369831967049 : Nat.Prime 941217369831967049 := by
  apply lucas_primality 941217369831967049 (3 : ZMod 941217369831967049)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5987767, 1), (19648755743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5987767, 1), (19648755743, 1)] : List FactorBlock).map factorBlockValue).prod) = 941217369831967049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5987767
      · exact prime_quintC_19648755743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 941217369831967049) ^ 470608684915983524 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 941217369831967049) ^ 157190045944 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 941217369831967049) ^ 47902136 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1778110061930112629 : Nat.Prime 1778110061930112629 := by
  apply lucas_primality 1778110061930112629 (2 : ZMod 1778110061930112629)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (108923, 1), (1167211, 1), (3496469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (108923, 1), (1167211, 1), (3496469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1778110061930112629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_108923
      · exact prime_quintC_1167211
      · exact prime_quintC_3496469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1778110061930112629) ^ 889055030965056314 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 16324468311836 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 1523383571548 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1778110061930112629) ^ 508544495012 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2072079488667149077 : Nat.Prime 2072079488667149077 := by
  apply lucas_primality 2072079488667149077 (2 : ZMod 2072079488667149077)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (239, 1), (263, 1), (119438318393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (239, 1), (263, 1), (119438318393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072079488667149077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_23
      · exact prime_quintC_239
      · exact prime_quintC_263
      · exact prime_quintC_119438318393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2072079488667149077) ^ 1036039744333574538 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072079488667149077) ^ 690693162889049692 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072079488667149077) ^ 90090412550745612 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072079488667149077) ^ 8669788655511084 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072079488667149077) ^ 7878629234475852 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072079488667149077) ^ 17348532 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2386674049794826901 : Nat.Prime 2386674049794826901 := by
  apply lucas_primality 2386674049794826901 (2 : ZMod 2386674049794826901)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (23866740497948269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (23866740497948269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2386674049794826901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_23866740497948269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2386674049794826901) ^ 1193337024897413450 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386674049794826901) ^ 477334809958965380 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386674049794826901) ^ 100 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2582665281154572547 : Nat.Prime 2582665281154572547 := by
  apply lucas_primality 2582665281154572547 (2 : ZMod 2582665281154572547)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (829, 1), (22575350790673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (829, 1), (22575350790673, 1)] : List FactorBlock).map factorBlockValue).prod) = 2582665281154572547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_23
      · exact prime_quintC_829
      · exact prime_quintC_22575350790673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2582665281154572547) ^ 1291332640577286273 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 860888427051524182 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 112289794832807502 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 3115398409112874 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2582665281154572547) ^ 114402 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_3775351412811012257 : Nat.Prime 3775351412811012257 := by
  apply lucas_primality 3775351412811012257 (3 : ZMod 3775351412811012257)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3775351412811012257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_52023863
      · exact prime_quintC_2267800291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3775351412811012257) ^ 1887675706405506128 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 72569609312 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 1664763616 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_5550769010340364621 : Nat.Prime 5550769010340364621 := by
  apply lucas_primality 5550769010340364621 (7 : ZMod 5550769010340364621)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (859, 1), (2417, 1), (9623, 1), (243707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (859, 1), (2417, 1), (9623, 1), (243707, 1)] : List FactorBlock).map factorBlockValue).prod) = 5550769010340364621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_19
      · exact prime_quintC_859
      · exact prime_quintC_2417
      · exact prime_quintC_9623
      · exact prime_quintC_243707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5550769010340364621) ^ 2775384505170182310 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 1850256336780121540 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 1110153802068072924 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 292145737386334980 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 6461896403190180 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 2296553169358860 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 576823133153940 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 5550769010340364621) ^ 22776403674660 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_5875008263295773599 : Nat.Prime 5875008263295773599 := by
  apply lucas_primality 5875008263295773599 (3 : ZMod 5875008263295773599)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (223, 1), (1463629363053257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (223, 1), (1463629363053257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5875008263295773599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_223
      · exact prime_quintC_1463629363053257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5875008263295773599) ^ 2937504131647886799 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 1958336087765257866 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 26345328534958626 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875008263295773599) ^ 4014 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_9883705415003947837 : Nat.Prime 9883705415003947837 := by
  apply lucas_primality 9883705415003947837 (2 : ZMod 9883705415003947837)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (1759, 1), (8214816212531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (1759, 1), (8214816212531, 1)] : List FactorBlock).map factorBlockValue).prod) = 9883705415003947837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_19
      · exact prime_quintC_1759
      · exact prime_quintC_8214816212531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9883705415003947837) ^ 4941852707501973918 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9883705415003947837) ^ 3294568471667982612 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9883705415003947837) ^ 520195021842313044 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9883705415003947837) ^ 5618934289371204 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9883705415003947837) ^ 1203156 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_19
      · exact prime_quintC_1823
      · exact prime_quintC_3271
      · exact prime_quintC_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_23
      · exact prime_quintC_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_14985857888517495907 : Nat.Prime 14985857888517495907 := by
  apply lucas_primality 14985857888517495907 (5 : ZMod 14985857888517495907)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (142151, 1), (158291451491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (142151, 1), (158291451491, 1)] : List FactorBlock).map factorBlockValue).prod) = 14985857888517495907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_37
      · exact prime_quintC_142151
      · exact prime_quintC_158291451491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14985857888517495907) ^ 7492928944258747953 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14985857888517495907) ^ 4995285962839165302 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14985857888517495907) ^ 405023186176148538 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14985857888517495907) ^ 105422106693006 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 14985857888517495907) ^ 94672566 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_15012789852106255987 : Nat.Prime 15012789852106255987 := by
  apply lucas_primality 15012789852106255987 (3 : ZMod 15012789852106255987)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 2), (19, 1), (43, 1), (504627554647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 2), (19, 1), (43, 1), (504627554647, 1)] : List FactorBlock).map factorBlockValue).prod) = 15012789852106255987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_43
      · exact prime_quintC_504627554647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15012789852106255987) ^ 7506394926053127993 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 5004263284035418662 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 2144684264586607998 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 883105285418015058 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 790146834321381894 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 349134647723401302 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 29750238 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_45023731903529596433 : Nat.Prime 45023731903529596433 := by
  apply lucas_primality 45023731903529596433 (3 : ZMod 45023731903529596433)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) = 45023731903529596433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_7411
      · exact prime_quintC_93287
      · exact prime_quintC_4070273261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45023731903529596433) ^ 22511865951764798216 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 6075257307182512 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 482636722196336 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 11061599312 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_58156383245098349833 : Nat.Prime 58156383245098349833 := by
  apply lucas_primality 58156383245098349833 (5 : ZMod 58156383245098349833)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (34129332890315933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (34129332890315933, 1)] : List FactorBlock).map factorBlockValue).prod) = 58156383245098349833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_71
      · exact prime_quintC_34129332890315933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58156383245098349833) ^ 29078191622549174916 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 19385461081699449944 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 819103989367582392 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58156383245098349833) ^ 1704 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_59302232490023687023 : Nat.Prime 59302232490023687023 := by
  apply lucas_primality 59302232490023687023 (3 : ZMod 59302232490023687023)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9883705415003947837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9883705415003947837, 1)] : List FactorBlock).map factorBlockValue).prod) = 59302232490023687023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_9883705415003947837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59302232490023687023) ^ 29651116245011843511 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 59302232490023687023) ^ 19767410830007895674 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 59302232490023687023) ^ 6 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_60632075843123951923 : Nat.Prime 60632075843123951923 := by
  apply lucas_primality 60632075843123951923 (2 : ZMod 60632075843123951923)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (43, 1), (227, 1), (340037, 1), (62134759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (43, 1), (227, 1), (340037, 1), (62134759, 1)] : List FactorBlock).map factorBlockValue).prod) = 60632075843123951923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_7
      · exact prime_quintC_43
      · exact prime_quintC_227
      · exact prime_quintC_340037
      · exact prime_quintC_62134759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60632075843123951923) ^ 30316037921561975961 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 20210691947707983974 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 8661725120446278846 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 1410048275421487254 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 267101655696581286 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 178310230484106 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60632075843123951923) ^ 975815740158 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_68933592817856129557 : Nat.Prime 68933592817856129557 := by
  apply lucas_primality 68933592817856129557 (2 : ZMod 68933592817856129557)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod) = 68933592817856129557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_12853
      · exact prime_quintC_148978605984457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68933592817856129557) ^ 34466796408928064778 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 22977864272618709852 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 5363229815440452 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 462708 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_76768245926690061509 : Nat.Prime 76768245926690061509 := by
  apply lucas_primality 76768245926690061509 (2 : ZMod 76768245926690061509)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (311, 1), (977, 1), (19993, 1), (3159284287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (311, 1), (977, 1), (19993, 1), (3159284287, 1)] : List FactorBlock).map factorBlockValue).prod) = 76768245926690061509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_311
      · exact prime_quintC_977
      · exact prime_quintC_19993
      · exact prime_quintC_3159284287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76768245926690061509) ^ 38384122963345030754 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 246843234490964828 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 78575482012988804 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 3839756211008356 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76768245926690061509) ^ 24299252284 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_101627574192727747903 : Nat.Prime 101627574192727747903 := by
  apply lucas_primality 101627574192727747903 (3 : ZMod 101627574192727747903)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) = 101627574192727747903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_3833
      · exact prime_quintC_1472991480313183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101627574192727747903) ^ 50813787096363873951 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 33875858064242582634 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 26513846645637294 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 68994 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_127937752325444133529 : Nat.Prime 127937752325444133529 := by
  apply lucas_primality 127937752325444133529 (11 : ZMod 127937752325444133529)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod) = 127937752325444133529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_127
      · exact prime_quintC_129951480466757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127937752325444133529) ^ 63968876162722066764 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 42645917441814711176 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 7525750136790831384 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 6733565911865480712 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 1007383876578300264 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 984504 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_460069275034891321889 : Nat.Prime 460069275034891321889 := by
  apply lucas_primality 460069275034891321889 (3 : ZMod 460069275034891321889)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 2), (8837243, 1), (13445318203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 2), (8837243, 1), (13445318203, 1)] : List FactorBlock).map factorBlockValue).prod) = 460069275034891321889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_8837243
      · exact prime_quintC_13445318203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 460069275034891321889) ^ 230034637517445660944 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 460069275034891321889) ^ 41824479548626483808 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 460069275034891321889) ^ 52060272082016 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 460069275034891321889) ^ 34217804896 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_953929693745394630791 : Nat.Prime 953929693745394630791 := by
  apply lucas_primality 953929693745394630791 (7 : ZMod 953929693745394630791)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod) = 953929693745394630791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_19
      · exact prime_quintC_73819
      · exact prime_quintC_344873
      · exact prime_quintC_197212943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 953929693745394630791) ^ 476964846872697315395 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 190785938749078926158 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 50206825986599717410 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 12922549665335410 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 2766031825470230 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 4837054197530 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1508017325915387268257 : Nat.Prime 1508017325915387268257 := by
  apply lucas_primality 1508017325915387268257 (3 : ZMod 1508017325915387268257)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (29, 1), (125497, 1), (1177151406131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (29, 1), (125497, 1), (1177151406131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508017325915387268257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_29
      · exact prime_quintC_125497
      · exact prime_quintC_1177151406131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1508017325915387268257) ^ 754008662957693634128 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508017325915387268257) ^ 137092484174126115296 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508017325915387268257) ^ 52000597445358181664 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508017325915387268257) ^ 12016361553785248 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508017325915387268257) ^ 1281073376 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2173973671256887784863 : Nat.Prime 2173973671256887784863 := by
  apply lucas_primality 2173973671256887784863 (3 : ZMod 2173973671256887784863)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (54542561, 1), (2214349910519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (54542561, 1), (2214349910519, 1)] : List FactorBlock).map factorBlockValue).prod) = 2173973671256887784863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_54542561
      · exact prime_quintC_2214349910519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2173973671256887784863) ^ 1086986835628443892431 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173973671256887784863) ^ 724657890418962594954 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173973671256887784863) ^ 39858298389342 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173973671256887784863) ^ 981766098 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_19
      · exact prime_quintC_107
      · exact prime_quintC_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_3888897644764009263853 : Nat.Prime 3888897644764009263853 := by
  apply lucas_primality 3888897644764009263853 (6 : ZMod 3888897644764009263853)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1657, 1), (1928743, 1), (11266937519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1657, 1), (1928743, 1), (11266937519, 1)] : List FactorBlock).map factorBlockValue).prod) = 3888897644764009263853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_1657
      · exact prime_quintC_1928743
      · exact prime_quintC_11266937519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3888897644764009263853) ^ 1944448822382004631926 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888897644764009263853) ^ 1296299214921336421284 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888897644764009263853) ^ 2346950902090530636 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888897644764009263853) ^ 2016286070650164 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888897644764009263853) ^ 345160132308 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_5553202817604011060269 : Nat.Prime 5553202817604011060269 := by
  apply lucas_primality 5553202817604011060269 (6 : ZMod 5553202817604011060269)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (870853, 1), (1033741, 1), (2168989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (870853, 1), (1033741, 1), (2168989, 1)] : List FactorBlock).map factorBlockValue).prod) = 5553202817604011060269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_79
      · exact prime_quintC_870853
      · exact prime_quintC_1033741
      · exact prime_quintC_2168989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5553202817604011060269) ^ 2776601408802005530134 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5553202817604011060269) ^ 1851067605868003686756 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5553202817604011060269) ^ 70293706551949507092 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5553202817604011060269) ^ 6376739607722556 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5553202817604011060269) ^ 5371947922742748 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5553202817604011060269) ^ 2560272466851612 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_8548184275924161516341 : Nat.Prime 8548184275924161516341 := by
  apply lucas_primality 8548184275924161516341 (13 : ZMod 8548184275924161516341)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (5550769010340364621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (5550769010340364621, 1)] : List FactorBlock).map factorBlockValue).prod) = 8548184275924161516341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_5550769010340364621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8548184275924161516341) ^ 4274092137962080758170 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 8548184275924161516341) ^ 1709636855184832303268 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 8548184275924161516341) ^ 1221169182274880216620 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 8548184275924161516341) ^ 777107661447651046940 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (13 : ZMod 8548184275924161516341) ^ 1540 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_12207876165556182456341 : Nat.Prime 12207876165556182456341 := by
  apply lucas_primality 12207876165556182456341 (2 : ZMod 12207876165556182456341)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (45119, 1), (13528531400913343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (45119, 1), (13528531400913343, 1)] : List FactorBlock).map factorBlockValue).prod) = 12207876165556182456341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_45119
      · exact prime_quintC_13528531400913343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12207876165556182456341) ^ 6103938082778091228170 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 2441575233111236491268 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 270570628018266860 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12207876165556182456341) ^ 902380 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_12378824676074916524737 : Nat.Prime 12378824676074916524737 := by
  apply lucas_primality 12378824676074916524737 (5 : ZMod 12378824676074916524737)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (43517, 1), (493853323129583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (43517, 1), (493853323129583, 1)] : List FactorBlock).map factorBlockValue).prod) = 12378824676074916524737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_43517
      · exact prime_quintC_493853323129583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12378824676074916524737) ^ 6189412338037458262368 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 4126274892024972174912 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 284459514122639808 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12378824676074916524737) ^ 25065792 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_21795107422726359259933 : Nat.Prime 21795107422726359259933 := by
  apply lucas_primality 21795107422726359259933 (5 : ZMod 21795107422726359259933)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (761, 1), (2386674049794826901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (761, 1), (2386674049794826901, 1)] : List FactorBlock).map factorBlockValue).prod) = 21795107422726359259933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_761
      · exact prime_quintC_2386674049794826901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21795107422726359259933) ^ 10897553711363179629966 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 21795107422726359259933) ^ 7265035807575453086644 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 21795107422726359259933) ^ 28640088597537922812 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 21795107422726359259933) ^ 9132 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_50862001673628381108359 : Nat.Prime 50862001673628381108359 := by
  apply lucas_primality 50862001673628381108359 (7 : ZMod 50862001673628381108359)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1697, 1), (14985857888517495907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1697, 1), (14985857888517495907, 1)] : List FactorBlock).map factorBlockValue).prod) = 50862001673628381108359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_1697
      · exact prime_quintC_14985857888517495907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 50862001673628381108359) ^ 25431000836814190554179 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 50862001673628381108359) ^ 29971715777034991814 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 50862001673628381108359) ^ 3394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_58528063569446646906503 : Nat.Prime 58528063569446646906503 := by
  apply lucas_primality 58528063569446646906503 (5 : ZMod 58528063569446646906503)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod) = 58528063569446646906503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_53
      · exact prime_quintC_97
      · exact prime_quintC_315283291
      · exact prime_quintC_18054505621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58528063569446646906503) ^ 29264031784723323453251 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 1104303086215974469934 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 603382098654089143366 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 185636426795122 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 3241742798062 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_79065530937124474520923 : Nat.Prime 79065530937124474520923 := by
  apply lucas_primality 79065530937124474520923 (2 : ZMod 79065530937124474520923)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod) = 79065530937124474520923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_103
      · exact prime_quintC_127937752325444133529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79065530937124474520923) ^ 39532765468562237260461 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 26355176979041491506974 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 767626513952664801174 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 618 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_105972077381845601404697 : Nat.Prime 105972077381845601404697 := by
  apply lucas_primality 105972077381845601404697 (3 : ZMod 105972077381845601404697)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (6521, 1), (12886453, 1), (3665940493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (6521, 1), (12886453, 1), (3665940493, 1)] : List FactorBlock).map factorBlockValue).prod) = 105972077381845601404697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_43
      · exact prime_quintC_6521
      · exact prime_quintC_12886453
      · exact prime_quintC_3665940493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105972077381845601404697) ^ 52986038690922800702348 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 105972077381845601404697) ^ 2464466915856874451272 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 105972077381845601404697) ^ 16250893633161417176 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 105972077381845601404697) ^ 8223525696469432 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 105972077381845601404697) ^ 28907200644472 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_301168454275224747175301 : Nat.Prime 301168454275224747175301 := by
  apply lucas_primality 301168454275224747175301 (3 : ZMod 301168454275224747175301)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod) = 301168454275224747175301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_241
      · exact prime_quintC_266957
      · exact prime_quintC_955333581581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 301168454275224747175301) ^ 150584227137612373587650 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 60233690855044949435060 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 43024064896460678167900 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1249661635996783183300 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1128153426489002900 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 315249521300 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1007384870571593615807227 : Nat.Prime 1007384870571593615807227 := by
  apply lucas_primality 1007384870571593615807227 (3 : ZMod 1007384870571593615807227)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2887, 1), (58156383245098349833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2887, 1), (58156383245098349833, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007384870571593615807227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_2887
      · exact prime_quintC_58156383245098349833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1007384870571593615807227) ^ 503692435285796807903613 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 335794956857197871935742 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 348938299470590098998 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007384870571593615807227) ^ 17322 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1065489261087619202876137 : Nat.Prime 1065489261087619202876137 := by
  apply lucas_primality 1065489261087619202876137 (7 : ZMod 1065489261087619202876137)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1599253, 1), (9253358886649121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1599253, 1), (9253358886649121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065489261087619202876137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_1599253
      · exact prime_quintC_9253358886649121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1065489261087619202876137) ^ 532744630543809601438068 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1065489261087619202876137) ^ 355163087029206400958712 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1065489261087619202876137) ^ 666241839838736712 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1065489261087619202876137) ^ 115146216 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1170561271388932938130061 : Nat.Prime 1170561271388932938130061 := by
  apply lucas_primality 1170561271388932938130061 (2 : ZMod 1170561271388932938130061)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170561271388932938130061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_5
      · exact prime_quintC_58528063569446646906503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1170561271388932938130061) ^ 585280635694466469065030 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 234112254277786587626012 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 20 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_36489718645148835417017333 : Nat.Prime 36489718645148835417017333 := by
  apply lucas_primality 36489718645148835417017333 (2 : ZMod 36489718645148835417017333)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod) = 36489718645148835417017333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_73
      · exact prime_quintC_131
      · exact prime_quintC_953929693745394630791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36489718645148835417017333) ^ 18244859322574417708508666 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 499859159522586786534484 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 278547470573655232190972 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 38252 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_61576400213688659766216751 : Nat.Prime 61576400213688659766216751 := by
  apply lucas_primality 61576400213688659766216751 (6 : ZMod 61576400213688659766216751)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 61576400213688659766216751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 61576400213688659766216751) ^ 30788200106844329883108375 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 20525466737896219922072250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 12315280042737731953243350 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 8796628601955522823745250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 5597854564880787251474250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 4736646170283743058939750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 3622141189040509398012750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 3240863169141508408748250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 2677234791899506946357250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 2123324145299608957455750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1986335490764150315039250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1664227032802396209897750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1501863419846064872346750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1432009307295085110842250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1310136174759333186515250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1161818871956389806909750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1043667800232011182478250 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (6 : ZMod 61576400213688659766216751) ^ 1009449183830961635511750 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_67946372649587486638584001 : Nat.Prime 67946372649587486638584001 := by
  apply lucas_primality 67946372649587486638584001 (58 : ZMod 67946372649587486638584001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 67946372649587486638584001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (58 : ZMod 67946372649587486638584001) ^ 33973186324793743319292000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 22648790883195828879528000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 13589274529917497327716800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 9706624664226783805512000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 6176942968144316967144000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 5226644049968268202968000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 3996845449975734508152000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 3576124876294078244136000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 2954190115199455940808000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 2191818472567338278664000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1836388449988850990232000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1657228601209450893624000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1580148201153197363688000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1445667503182712481672000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1282007031124292200728000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1151633434738770959976000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (58 : ZMod 67946372649587486638584001) ^ 1113874961468647321944000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_69545110829577780441844801 : Nat.Prime 69545110829577780441844801 := by
  apply lucas_primality 69545110829577780441844801 (17 : ZMod 69545110829577780441844801)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 69545110829577780441844801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 69545110829577780441844801) ^ 34772555414788890220922400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 23181703609859260147281600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 13909022165915556088368960 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 9935015832796825777406400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 6322282802688889131076800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 5349623909967521572449600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 3660268991030409496939200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 3023700470851207845297600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 2398107269985440704891200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 2243390671921863885220800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1879597589988588660590400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1696222215355555620532800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1617328158827390242833600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1479683209139952775358400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1312171902444863781921600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1178730692026742041387200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1140083784091439023636800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_70373028815644182589962001 : Nat.Prime 70373028815644182589962001 := by
  apply lucas_primality 70373028815644182589962001 (67 : ZMod 70373028815644182589962001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 70373028815644182589962001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 70373028815644182589962001) ^ 35186514407822091294981000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 23457676271881394196654000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 14074605763128836517992400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 10053289830806311798566000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 6397548074149471144542000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 5413309908895706353074000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 4139589930332010740586000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 3703843621876009609998000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 3059696905028007938694000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 2426656166056695951378000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 2270097703730457502902000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1901973751774167097026000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1716415336966931282682000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1636582065480097269534000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1497298485439237927446000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1327792996521588350754000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1192763200265155637118000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 70373028815644182589962001) ^ 1153656210092527583442000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_72979437290297670834034667 : Nat.Prime 72979437290297670834034667 := by
  apply lucas_primality 72979437290297670834034667 (2 : ZMod 72979437290297670834034667)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod) = 72979437290297670834034667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_36489718645148835417017333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72979437290297670834034667) ^ 36489718645148835417017333 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72979437290297670834034667) ^ 2 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_76770576889793653734504001 : Nat.Prime 76770576889793653734504001 := by
  apply lucas_primality 76770576889793653734504001 (11 : ZMod 76770576889793653734504001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 76770576889793653734504001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 76770576889793653734504001) ^ 38385288444896826867252000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 25590192296597884578168000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 15354115377958730746900800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 10967225269970521962072000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 5905428991522588748808000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 4515916287634920807912000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 4040556678410192301816000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 3337851169121463205848000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 2647261272061850128776000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 2476470222251408184984000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 2074880456480909560392000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1872453094873015944744000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1785362253251015203128000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1633416529570077739032000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1448501450750823655368000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1301196218471078876856000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76770576889793653734504001) ^ 1258534047373666454664000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_79882897574515018075092001 : Nat.Prime 79882897574515018075092001 := by
  apply lucas_primality 79882897574515018075092001 (79 : ZMod 79882897574515018075092001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 79882897574515018075092001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 79882897574515018075092001) ^ 39941448787257509037546000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 26627632524838339358364000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 15976579514903003615018400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 11411842510645002582156000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 7262081597683183461372000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 6144838274962693698084000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 4698993974971471651476000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 4204363030237632530268000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 3473169459761522525004000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 2754582674983276485348000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 2576867663694032841132000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1948363355475976050612000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1857741804058488792444000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1699636118606702512236000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1507224482538019208964000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1353947416517203696188000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (79 : ZMod 79882897574515018075092001) ^ 1309555697942869148772000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_85671513340784222283432001 : Nat.Prime 85671513340784222283432001 := by
  apply lucas_primality 85671513340784222283432001 (97 : ZMod 85671513340784222283432001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 85671513340784222283432001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 85671513340784222283432001) ^ 42835756670392111141716000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 28557171113594740761144000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 17134302668156844456686400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 12238787620112031754776000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 7788319394616747480312000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 6590116410829555560264000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 5039500784752013075496000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 4509027017936011699128000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 2954190115199455940808000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 2763597204541426525272000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 2315446306507681683336000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 2089549105872785909352000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 1992360775367074936824000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 1822798156186898346456000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 1616443647939324948744000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 1452059548148885123448000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (97 : ZMod 85671513340784222283432001) ^ 1404451038373511840712000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_107478807645711115228305601 : Nat.Prime 107478807645711115228305601 := by
  apply lucas_primality 107478807645711115228305601 (67 : ZMod 107478807645711115228305601)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 107478807645711115228305601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 107478807645711115228305601) ^ 53739403822855557614152800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 35826269215237038409435200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 21495761529142223045661120 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 15354115377958730746900800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 8267600588131624248331200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 6322282802688889131076800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 5656779349774269222542400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 4672991636770048488187200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3706165780886590180286400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3467058311151971458977600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2904832639073273384548800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2621434332822222322641600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2499507154551421284379200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2286783141398108834644800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2027902031051153117515200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1821674705859510427598400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1761947666323133036529600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_111534611707813421463336001 : Nat.Prime 111534611707813421463336001 := by
  apply lucas_primality 111534611707813421463336001 (89 : ZMod 111534611707813421463336001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 111534611707813421463336001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 111534611707813421463336001) ^ 55767305853906710731668000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 37178203902604473821112000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 22306922341562684292667200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 15933515958259060209048000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 10139510155255765587576000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 8579585515985647804872000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 6560859512224318909608000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 5870242721463864287544000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 4849330943817974846232000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 3846021093372876602184000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 3597890700252045853656000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 3014448965076038417928000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 2720356383117400523496000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 2593828179251474917752000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 2373076844847094073688000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 1890417147590057990904000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (89 : ZMod 111534611707813421463336001) ^ 1828436257505138056776000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_131362987122535807501262401 : Nat.Prime 131362987122535807501262401 := by
  apply lucas_primality 131362987122535807501262401 (71 : ZMod 131362987122535807501262401)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 131362987122535807501262401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 131362987122535807501262401) ^ 65681493561267903750631200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 43787662374178602500420800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 26272597424507161500252480 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 18766141017505115357323200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 11942089738412346136478400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 10104845163271985192404800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 7727234536619753382427200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 6913841427501884605329600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 5711434222718948152228800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4529758176639165775905600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4237515713630187338750400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3550351003311778581115200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3203975295671605061006400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3054953188896181569796800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2794957172819910797899200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2478546926840298254740800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2226491307161623855953600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2153491592172718155758400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_159765795149030036150184001 : Nat.Prime 159765795149030036150184001 := by
  apply lucas_primality 159765795149030036150184001 (71 : ZMod 159765795149030036150184001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 159765795149030036150184001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 159765795149030036150184001) ^ 79882897574515018075092000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 53255265049676678716728000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 31953159029806007230036800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 22823685021290005164312000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 14524163195366366922744000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 12289676549925387396168000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 9397987949942943302952000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 8408726060475265060536000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 6946338919523045050008000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 5509165349966552970696000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 5153735327388065682264000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3896726710951952101224000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3715483608116977584888000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3399272237213405024472000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 3014448965076038417928000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 2707894833034407392376000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (71 : ZMod 159765795149030036150184001) ^ 2619111395885738297544000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_218938311870893012502104003 : Nat.Prime 218938311870893012502104003 := by
  apply lucas_primality 218938311870893012502104003 (2 : ZMod 218938311870893012502104003)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1033, 1), (105972077381845601404697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1033, 1), (105972077381845601404697, 1)] : List FactorBlock).map factorBlockValue).prod) = 218938311870893012502104003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_1033
      · exact prime_quintC_105972077381845601404697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 218938311870893012502104003) ^ 109469155935446506251052001 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 218938311870893012502104003) ^ 211944154763691202809394 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (2 : ZMod 218938311870893012502104003) ^ 2066 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_246305600854754639064867001 : Nat.Prime 246305600854754639064867001 := by
  apply lucas_primality 246305600854754639064867001 (103 : ZMod 246305600854754639064867001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 246305600854754639064867001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 246305600854754639064867001) ^ 123152800427377319532433500 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 82101866951584879688289000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 49261120170950927812973400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 35186514407822091294981000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 22391418259523149005897000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 18946584681134972235759000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 14488564756162037592051000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 12963452676566033634993000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 10708939167598027785429000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 8493296581198435829823000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 7945341963056601260157000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6656908131209584839591000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6007453679384259489387000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5728037229180340443369000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5240544699037332746061000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4647275487825559227639000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4174671200928044729913000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4037796735323846542047000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_3
      · exact prime_quintC_5
      · exact prime_quintC_7
      · exact prime_quintC_11
      · exact prime_quintC_13
      · exact prime_quintC_17
      · exact prime_quintC_19
      · exact prime_quintC_23
      · exact prime_quintC_29
      · exact prime_quintC_31
      · exact prime_quintC_37
      · exact prime_quintC_41
      · exact prime_quintC_43
      · exact prime_quintC_47
      · exact prime_quintC_53
      · exact prime_quintC_59
      · exact prime_quintC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem prime_quintC_5911334420514111337556808089 : Nat.Prime 5911334420514111337556808089 := by
  apply lucas_primality 5911334420514111337556808089 (3 : ZMod 5911334420514111337556808089)
  · rw [← quintCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (146009, 1), (460069275034891321889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (146009, 1), (460069275034891321889, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quintC_2
      · exact prime_quintC_11
      · exact prime_quintC_146009
      · exact prime_quintC_460069275034891321889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5911334420514111337556808089) ^ 2955667210257055668778404044 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111337556808089) ^ 537394038228555576141528008 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111337556808089) ^ 40486096203070436326232 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5911334420514111337556808089) ^ 12848792 ≠ 1
      rw [← quintCFastPow_eq_pow]
      decide

private theorem phi_quintC_5911334420514111337556808000 : Nat.totient 5911334420514111337556808000 = 777856842296803196928000000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_5, prime_quintC_7, prime_quintC_11, prime_quintC_13, prime_quintC_17, prime_quintC_19, prime_quintC_23, prime_quintC_29, prime_quintC_31, prime_quintC_37, prime_quintC_41, prime_quintC_43, prime_quintC_47, prime_quintC_53, prime_quintC_59, prime_quintC_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808001 : Nat.totient 5911334420514111337556808001 = 5911293274574380552724110512 := by
  rw [← show ((([(143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_143669, prime_quintC_13852339783, prime_quintC_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808002 : Nat.totient 5911334420514111337556808002 = 2941808575791226459815074304 := by
  rw [← show ((([(2, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_223, prime_quintC_5113, prime_quintC_101287, prime_quintC_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808003 : Nat.totient 5911334420514111337556808003 = 3886904484868391081403667200 := by
  rw [← show ((([(3, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_73, prime_quintC_13737811, prime_quintC_68784581, prime_quintC_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808004 : Nat.totient 5911334420514111337556808004 = 2955667210257055668778404000 := by
  rw [← show ((([(2, 2), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808005 : Nat.totient 5911334420514111337556808005 = 4682219311413182558003904768 := by
  rw [← show ((([(5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_103, prime_quintC_5009, prime_quintC_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808006 : Nat.totient 5911334420514111337556808006 = 1960256053834675663766740992 := by
  rw [← show ((([(2, 1), (3, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_283, prime_quintC_613, prime_quintC_85303, prime_quintC_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808007 : Nat.totient 5911334420514111337556808007 = 5021926290412878865174732800 := by
  rw [← show ((([(7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_7, prime_quintC_113, prime_quintC_54421, prime_quintC_97654321, prime_quintC_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808008 : Nat.totient 5911334420514111337556808008 = 2920054697715968577072985600 := by
  rw [← show ((([(2, 3), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_83, prime_quintC_1433741, prime_quintC_106163831, prime_quintC_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808009 : Nat.totient 5911334420514111337556808009 = 3933854863788684518599788288 := by
  rw [← show ((([(3, 2), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_569, prime_quintC_37039, prime_quintC_1544987, prime_quintC_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808010 : Nat.totient 5911334420514111337556808010 = 2364533766271648981528824400 := by
  rw [← show ((([(2, 1), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_1222615931, prime_quintC_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808011 : Nat.totient 5911334420514111337556808011 = 5298251080928055058366958400 := by
  rw [← show ((([(11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_11, prime_quintC_71, prime_quintC_26687336297, prime_quintC_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808012 : Nat.totient 5911334420514111337556808012 = 1952364767209673858937268992 := by
  rw [← show ((([(2, 2), (3, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_109, prime_quintC_762563, prime_quintC_500452427, prime_quintC_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808013 : Nat.totient 5911334420514111337556808013 = 5444337797574560906077056000 := by
  rw [← show ((([(13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_13, prime_quintC_599, prime_quintC_1811, prime_quintC_33809, prime_quintC_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808014 : Nat.totient 5911334420514111337556808014 = 2533429035847318967660010624 := by
  rw [← show ((([(2, 1), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_7, prime_quintC_1671268889, prime_quintC_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808015 : Nat.totient 5911334420514111337556808015 = 3152711690940859380030297600 := by
  rw [← show ((([(3, 1), (5, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_5, prime_quintC_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808016 : Nat.totient 5911334420514111337556808016 = 2955667203431259456620100096 := by
  rw [← show ((([(2, 4), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_433014277, prime_quintC_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808017 : Nat.totient 5911334420514111337556808017 = 5563607240325035351648872512 := by
  rw [← show ((([(17, 1), (3421567, 1), (101627574192727747903, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_17, prime_quintC_3421567, prime_quintC_101627574192727747903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808018 : Nat.totient 5911334420514111337556808018 = 1970444536695645691297592832 := by
  rw [← show ((([(2, 1), (3, 2), (7294097, 1), (45023731903529596433, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_7294097, prime_quintC_45023731903529596433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808019 : Nat.totient 5911334420514111337556808019 = 5600211555672956774409463296 := by
  rw [← show ((([(19, 1), (9278485297, 1), (33531643827487633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_19, prime_quintC_9278485297, prime_quintC_33531643827487633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808020 : Nat.totient 5911334420514111337556808020 = 2364533655236198298650382336 := by
  rw [← show ((([(2, 2), (5, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_20930737, prime_quintC_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808021 : Nat.totient 5911334420514111337556808021 = 3313933950734047119790080000 := by
  rw [← show ((([(3, 1), (7, 1), (97, 1), (139, 1), (659, 1), (55001, 1), (576001613200633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_7, prime_quintC_97, prime_quintC_139, prime_quintC_659, prime_quintC_55001, prime_quintC_576001613200633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808022 : Nat.totient 5911334420514111337556808022 = 2685088065202949206055942400 := by
  rw [← show ((([(2, 1), (11, 1), (1471, 1), (48383, 1), (3775351412811012257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_11, prime_quintC_1471, prime_quintC_48383, prime_quintC_3775351412811012257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808023 : Nat.totient 5911334420514111337556808023 = 5654319691825232192232981216 := by
  rw [← show ((([(23, 1), (56297287, 1), (64144099, 1), (71172712477, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_23, prime_quintC_56297287, prime_quintC_64144099, prime_quintC_71172712477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808024 : Nat.totient 5911334420514111337556808024 = 1970444806838037112518936000 := by
  rw [← show ((([(2, 3), (3, 1), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_246305600854754639064867001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808025 : Nat.totient 5911334420514111337556808025 = 4729067528857841659119593040 := by
  rw [← show ((([(5, 2), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_626080687, prime_quintC_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808026 : Nat.totient 5911334420514111337556808026 = 2728308193972179846331286064 := by
  rw [← show ((([(2, 1), (13, 1), (24522826583, 1), (9271321778674247, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_13, prime_quintC_24522826583, prime_quintC_9271321778674247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808027 : Nat.totient 5911334420514111337556808027 = 3940889613676074225037871964 := by
  rw [← show ((([(3, 4), (72979437290297670834034667, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_72979437290297670834034667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808028 : Nat.totient 5911334420514111337556808028 = 2529815015911887876272520000 := by
  rw [← show ((([(2, 2), (7, 1), (701, 1), (301168454275224747175301, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_7, prime_quintC_701, prime_quintC_301168454275224747175301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808029 : Nat.totient 5911334420514111337556808029 = 5642483946057389443548856320 := by
  rw [← show ((([(29, 1), (89, 1), (6397, 1), (894938237, 1), (400062744481, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_29, prime_quintC_89, prime_quintC_6397, prime_quintC_894938237, prime_quintC_400062744481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808030 : Nat.totient 5911334420514111337556808030 = 1572466828560993711443107584 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_5, prime_quintC_409, prime_quintC_45127, prime_quintC_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808031 : Nat.totient 5911334420514111337556808031 = 5720533497321772806330600960 := by
  rw [← show ((([(31, 1), (50753, 1), (9003352679, 1), (417309099223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_31, prime_quintC_50753, prime_quintC_9003352679, prime_quintC_417309099223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808032 : Nat.totient 5911334420514111337556808032 = 2955469149062238470113769472 := by
  rw [← show ((([(2, 5), (14923, 1), (12378824676074916524737, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_14923, prime_quintC_12378824676074916524737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808033 : Nat.totient 5911334420514111337556808033 = 3549131971912506178150378560 := by
  rw [← show ((([(3, 1), (11, 1), (107, 1), (284957, 1), (5875008263295773599, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_11, prime_quintC_107, prime_quintC_284957, prime_quintC_5875008263295773599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808034 : Nat.totient 5911334420514111337556808034 = 2734491347364382985990707200 := by
  rw [← show ((([(2, 1), (17, 1), (79, 1), (227, 1), (3222797, 1), (3008297016953401, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_17, prime_quintC_79, prime_quintC_227, prime_quintC_3222797, prime_quintC_3008297016953401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808035 : Nat.totient 5911334420514111337556808035 = 4044693647204004540427678080 := by
  rw [← show ((([(5, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_7, prime_quintC_461, prime_quintC_13492702567, prime_quintC_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808036 : Nat.totient 5911334420514111337556808036 = 1958356188391177989129247344 := by
  rw [← show ((([(2, 2), (3, 2), (163, 1), (1007384870571593615807227, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_163, prime_quintC_1007384870571593615807227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808037 : Nat.totient 5911334420514111337556808037 = 5751568625365081301406624000 := by
  rw [← show ((([(37, 1), (159765795149030036150184001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_37, prime_quintC_159765795149030036150184001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808038 : Nat.totient 5911334420514111337556808038 = 2783313987943966416197108928 := by
  rw [← show ((([(2, 1), (19, 2), (167, 1), (115319, 1), (5026759, 1), (84575179597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_19, prime_quintC_167, prime_quintC_115319, prime_quintC_5026759, prime_quintC_84575179597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808039 : Nat.totient 5911334420514111337556808039 = 3637744258430281606526426208 := by
  rw [← show ((([(3, 1), (13, 1), (10464329423, 1), (14484700483141487, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_13, prime_quintC_10464329423, prime_quintC_14484700483141487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808040 : Nat.totient 5911334420514111337556808040 = 2352154001917303943676602880 := by
  rw [← show ((([(2, 3), (5, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_191, prime_quintC_282045737, prime_quintC_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808041 : Nat.totient 5911334420514111337556808041 = 5767155461084486629363596160 := by
  rw [← show ((([(41, 1), (81085469, 1), (1778110061930112629, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_41, prime_quintC_81085469, prime_quintC_1778110061930112629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808042 : Nat.totient 5911334420514111337556808042 = 1688951770356509261856349248 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1833389, 1), (76768245926690061509, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_7, prime_quintC_1833389, prime_quintC_76768245926690061509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808043 : Nat.totient 5911334420514111337556808043 = 5773348796214829807252312800 := by
  rw [← show ((([(43, 1), (11261, 1), (12207876165556182456341, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_43, prime_quintC_11261, prime_quintC_12207876165556182456341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808044 : Nat.totient 5911334420514111337556808044 = 2686949431993373834368366560 := by
  rw [← show ((([(2, 2), (11, 2), (129439, 1), (7795619827, 1), (12103873247, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_11, prime_quintC_129439, prime_quintC_7795619827, prime_quintC_12103873247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808045 : Nat.totient 5911334420514111337556808045 = 3152711690940859380030297600 := by
  rw [← show ((([(3, 2), (5, 1), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_5, prime_quintC_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808046 : Nat.totient 5911334420514111337556808046 = 2805225110242424528535676800 := by
  rw [← show ((([(2, 1), (23, 1), (131, 1), (8221, 1), (230189, 1), (518378746886659, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_23, prime_quintC_131, prime_quintC_8221, prime_quintC_230189, prime_quintC_518378746886659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808047 : Nat.totient 5911334420514111337556808047 = 5750533669087696697303531520 := by
  rw [← show ((([(47, 1), (337, 1), (449, 1), (1163, 1), (90191, 1), (7924438741469, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_47, prime_quintC_337, prime_quintC_449, prime_quintC_1163, prime_quintC_90191, prime_quintC_7924438741469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808048 : Nat.totient 5911334420514111337556808048 = 1970444765515392613282825152 := by
  rw [← show ((([(2, 4), (3, 1), (47684383, 1), (2582665281154572547, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_47684383, prime_quintC_2582665281154572547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808049 : Nat.totient 5911334420514111337556808049 = 5066813447778688107235788096 := by
  rw [← show ((([(7, 2), (118687, 1), (2617129, 1), (388383853927687, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_7, prime_quintC_118687, prime_quintC_2617129, prime_quintC_388383853927687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808050 : Nat.totient 5911334420514111337556808050 = 2341122542777865876260120000 := by
  rw [← show ((([(2, 1), (5, 2), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_101, prime_quintC_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808051 : Nat.totient 5911334420514111337556808051 = 3709072547458525785001392128 := by
  rw [← show ((([(3, 1), (17, 1), (123147449, 1), (941217369831967049, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_17, prime_quintC_123147449, prime_quintC_941217369831967049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808052 : Nat.totient 5911334420514111337556808052 = 2721435791543775783925696512 := by
  rw [← show ((([(2, 2), (13, 1), (397, 1), (30336529, 1), (9438995739323077, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_13, prime_quintC_397, prime_quintC_30336529, prime_quintC_9438995739323077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808053 : Nat.totient 5911334420514111337556808053 = 5799799808806297916093472000 := by
  rw [← show ((([(53, 1), (111534611707813421463336001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_53, prime_quintC_111534611707813421463336001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808054 : Nat.totient 5911334420514111337556808054 = 1968537309445163891693632896 := by
  rw [← show ((([(2, 1), (3, 3), (1033, 1), (105972077381845601404697, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_1033, prime_quintC_105972077381845601404697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808055 : Nat.totient 5911334420514111337556808055 = 4299152305828444609132224000 := by
  rw [← show ((([(5, 1), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_11, prime_quintC_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808056 : Nat.totient 5911334420514111337556808056 = 2491132493801104073920935936 := by
  rw [← show ((([(2, 3), (7, 1), (67, 1), (557, 1), (671633, 1), (4211487129410863, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_7, prime_quintC_67, prime_quintC_557, prime_quintC_671633, prime_quintC_4211487129410863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808057 : Nat.totient 5911334420514111337556808057 = 3731643338790767065158009744 := by
  rw [← show ((([(3, 1), (19, 1), (2039, 1), (50862001673628381108359, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_19, prime_quintC_2039, prime_quintC_50862001673628381108359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808058 : Nat.totient 5911334420514111337556808058 = 2843070446203496466660634624 := by
  rw [← show ((([(2, 1), (29, 1), (269, 1), (41609, 1), (19230437, 1), (473509638713, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_29, prime_quintC_269, prime_quintC_41609, prime_quintC_19230437, prime_quintC_473509638713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808059 : Nat.totient 5911334420514111337556808059 = 5809878195461320135201553376 := by
  rw [← show ((([(59, 1), (4597, 1), (21795107422726359259933, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_59, prime_quintC_4597, prime_quintC_21795107422726359259933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808060 : Nat.totient 5911334420514111337556808060 = 1571285768495580038334904320 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_5, prime_quintC_311, prime_quintC_1115447, prime_quintC_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808061 : Nat.totient 5911334420514111337556808061 = 5796861053084401761592560000 := by
  rw [← show ((([(61, 1), (331, 1), (35061805481, 1), (8350133606891, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_61, prime_quintC_331, prime_quintC_35061805481, prime_quintC_8350133606891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808062 : Nat.totient 5911334420514111337556808062 = 2860206439771033533377868960 := by
  rw [← show ((([(2, 1), (31, 1), (24517, 1), (3888897644764009263853, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_31, prime_quintC_24517, prime_quintC_3888897644764009263853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808063 : Nat.totient 5911334420514111337556808063 = 3377904997463898070092319872 := by
  rw [← show ((([(3, 2), (7, 1), (8994889, 1), (336377203, 1), (31011488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_7, prime_quintC_8994889, prime_quintC_336377203, prime_quintC_31011488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808064 : Nat.totient 5911334420514111337556808064 = 2955663329804201708796733440 := by
  rw [← show ((([(2, 7), (761681, 1), (60632075843123951923, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_761681, prime_quintC_60632075843123951923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808065 : Nat.totient 5911334420514111337556808065 = 4365289801721042345961328896 := by
  rw [← show ((([(5, 1), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_13, prime_quintC_1319293, prime_quintC_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808066 : Nat.totient 5911334420514111337556808066 = 1791283300415333612725207040 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (59393, 1), (1508017325915387268257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_11, prime_quintC_59393, prime_quintC_1508017325915387268257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808067 : Nat.totient 5911334420514111337556808067 = 5911334420499342269708331240 := by
  rw [← show ((([(400261864237, 1), (14768667586612591, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_400261864237, prime_quintC_14768667586612591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808068 : Nat.totient 5911334420514111337556808068 = 2781804433111227207182444544 := by
  rw [← show ((([(2, 2), (17, 1), (38699181337, 1), (2246336628673273, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_17, prime_quintC_38699181337, prime_quintC_2246336628673273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808069 : Nat.totient 5911334420514111337556808069 = 3769546586994505780471008000 := by
  rw [← show ((([(3, 1), (23, 1), (85671513340784222283432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_23, prime_quintC_85671513340784222283432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808070 : Nat.totient 5911334420514111337556808070 = 2019318916409645727744000000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_7, prime_quintC_433, prime_quintC_751, prime_quintC_39551, prime_quintC_40376737, prime_quintC_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808071 : Nat.totient 5911334420514111337556808071 = 5911325872329835413394600200 := by
  rw [← show ((([(691531, 1), (8548184275924161516341, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_691531, prime_quintC_8548184275924161516341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808072 : Nat.totient 5911334420514111337556808072 = 1969048042007701475690496000 := by
  rw [← show ((([(2, 3), (3, 2), (1601, 1), (11903, 1), (3469177, 1), (1241877643471, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_1601, prime_quintC_11903, prime_quintC_3469177, prime_quintC_1241877643471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808073 : Nat.totient 5911334420514111337556808073 = 5883318610685035948407766080 := by
  rw [← show ((([(211, 1), (854109329, 1), (32801190655096067, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_211, prime_quintC_854109329, prime_quintC_32801190655096067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808074 : Nat.totient 5911334420514111337556808074 = 2875784312682540650703312000 := by
  rw [← show ((([(2, 1), (37, 1), (79882897574515018075092001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_37, prime_quintC_79882897574515018075092001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808075 : Nat.totient 5911334420514111337556808075 = 3152711090429265295570056480 := by
  rw [← show ((([(3, 1), (5, 2), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_5, prime_quintC_5250043, prime_quintC_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808076 : Nat.totient 5911334420514111337556808076 = 2761748164739108973854944512 := by
  rw [← show ((([(2, 2), (19, 1), (73, 1), (1065489261087619202876137, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_19, prime_quintC_73, prime_quintC_1065489261087619202876137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808077 : Nat.totient 5911334420514111337556808077 = 4606234613387619224070240000 := by
  rw [← show ((([(7, 1), (11, 1), (76770576889793653734504001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_7, prime_quintC_11, prime_quintC_76770576889793653734504001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808078 : Nat.totient 5911334420514111337556808078 = 1818316069277180919692952960 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (3271, 1), (12061008403, 1), (1920997335277, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_13, prime_quintC_3271, prime_quintC_12061008403, prime_quintC_1920997335277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808079 : Nat.totient 5911334420514111337556808079 = 5886394986660251723884080000 := by
  rw [← show ((([(251, 1), (4241, 1), (5553202817604011060269, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_251, prime_quintC_4241, prime_quintC_5553202817604011060269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808080 : Nat.totient 5911334420514111337556808080 = 2364533768193799604402617344 := by
  rw [← show ((([(2, 4), (5, 1), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_5, prime_quintC_199731886537, prime_quintC_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808081 : Nat.totient 5911334420514111337556808081 = 3940889613676074225037872036 := by
  rw [← show ((([(3, 3), (218938311870893012502104003, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_218938311870893012502104003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808082 : Nat.totient 5911334420514111337556808082 = 2842962819609304848663424000 := by
  rw [← show ((([(2, 1), (41, 1), (71, 1), (2453597, 1), (187518491, 1), (2206815353, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_41, prime_quintC_71, prime_quintC_2453597, prime_quintC_187518491, prime_quintC_2206815353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808083 : Nat.totient 5911334420514111337556808083 = 5911240205384620530222614400 := by
  rw [← show ((([(66301, 1), (1169137, 1), (76260569734215359, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_66301, prime_quintC_1169137, prime_quintC_76260569734215359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808084 : Nat.totient 5911334420514111337556808084 = 1688952691575460382159088000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (70373028815644182589962001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_7, prime_quintC_70373028815644182589962001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808085 : Nat.totient 5911334420514111337556808085 = 4450887093092977948278067200 := by
  rw [← show ((([(5, 1), (17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_17, prime_quintC_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808086 : Nat.totient 5911334420514111337556808086 = 2886928272813127002414439464 := by
  rw [← show ((([(2, 1), (43, 1), (1159087, 1), (59302232490023687023, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_43, prime_quintC_1159087, prime_quintC_59302232490023687023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808087 : Nat.totient 5911334420514111337556808087 = 3804996868376899251760704000 := by
  rw [← show ((([(3, 1), (29, 1), (67946372649587486638584001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_29, prime_quintC_67946372649587486638584001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808088 : Nat.totient 5911334420514111337556808088 = 2686951788371776485048924160 := by
  rw [← show ((([(2, 3), (11, 1), (146009, 1), (460069275034891321889, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_11, prime_quintC_146009, prime_quintC_460069275034891321889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808089 : Nat.totient 5911334420514111337556808089 = 5911334420514111337556808088 := by
  rw [← show ((([(5911334420514111337556808089, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5911334420514111337556808089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808090 : Nat.totient 5911334420514111337556808090 = 1573488016390734215675904000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_5, prime_quintC_1051, prime_quintC_1153, prime_quintC_940369, prime_quintC_6947861, prime_quintC_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808091 : Nat.totient 5911334420514111337556808091 = 4620736928195024252736147840 := by
  rw [← show ((([(7, 1), (13, 1), (83, 1), (377711, 1), (2072079488667149077, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_7, prime_quintC_13, prime_quintC_83, prime_quintC_377711, prime_quintC_2072079488667149077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808092 : Nat.totient 5911334420514111337556808092 = 2827159908471632829433092480 := by
  rw [← show ((([(2, 2), (23, 1), (169181863, 1), (209339407, 1), (1814232361, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_23, prime_quintC_169181863, prime_quintC_209339407, prime_quintC_1814232361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808093 : Nat.totient 5911334420514111337556808093 = 3805933004366305347230068800 := by
  rw [← show ((([(3, 1), (31, 1), (487, 1), (137253738091, 1), (950931947653, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_3, prime_quintC_31, prime_quintC_487, prime_quintC_137253738091, prime_quintC_950931947653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808094 : Nat.totient 5911334420514111337556808094 = 2892680671079729858986237752 := by
  rw [← show ((([(2, 1), (47, 1), (28927, 1), (2173973671256887784863, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_47, prime_quintC_28927, prime_quintC_2173973671256887784863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808095 : Nat.totient 5911334420514111337556808095 = 4474476526793748262088017824 := by
  rw [← show ((([(5, 1), (19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_5, prime_quintC_19, prime_quintC_787, prime_quintC_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808096 : Nat.totient 5911334420514111337556808096 = 1970444806838037112518936000 := by
  rw [← show ((([(2, 5), (3, 1), (61576400213688659766216751, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_2, prime_quintC_3, prime_quintC_61576400213688659766216751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quintC_5911334420514111337556808097 : Nat.totient 5911334420514111337556808097 = 5911334420470096856418822420 := by
  rw [← show ((([(134304717571, 1), (44014346833268107, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911334420514111337556808097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quintC_134304717571, prime_quintC_44014346833268107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64QuintC : certifiedKill 1 5911334420514111337556807999 96 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_quintC_5911334420514111337556808000, phi_quintC_5911334420514111337556808001, phi_quintC_5911334420514111337556808002,
    phi_quintC_5911334420514111337556808003, phi_quintC_5911334420514111337556808004, phi_quintC_5911334420514111337556808005,
    phi_quintC_5911334420514111337556808006, phi_quintC_5911334420514111337556808007, phi_quintC_5911334420514111337556808008,
    phi_quintC_5911334420514111337556808009, phi_quintC_5911334420514111337556808010, phi_quintC_5911334420514111337556808011,
    phi_quintC_5911334420514111337556808012, phi_quintC_5911334420514111337556808013, phi_quintC_5911334420514111337556808014,
    phi_quintC_5911334420514111337556808015, phi_quintC_5911334420514111337556808016, phi_quintC_5911334420514111337556808017,
    phi_quintC_5911334420514111337556808018, phi_quintC_5911334420514111337556808019, phi_quintC_5911334420514111337556808020,
    phi_quintC_5911334420514111337556808021, phi_quintC_5911334420514111337556808022, phi_quintC_5911334420514111337556808023,
    phi_quintC_5911334420514111337556808024, phi_quintC_5911334420514111337556808025, phi_quintC_5911334420514111337556808026,
    phi_quintC_5911334420514111337556808027, phi_quintC_5911334420514111337556808028, phi_quintC_5911334420514111337556808029,
    phi_quintC_5911334420514111337556808030, phi_quintC_5911334420514111337556808031, phi_quintC_5911334420514111337556808032,
    phi_quintC_5911334420514111337556808033, phi_quintC_5911334420514111337556808034, phi_quintC_5911334420514111337556808035,
    phi_quintC_5911334420514111337556808036, phi_quintC_5911334420514111337556808037, phi_quintC_5911334420514111337556808038,
    phi_quintC_5911334420514111337556808039, phi_quintC_5911334420514111337556808040, phi_quintC_5911334420514111337556808041,
    phi_quintC_5911334420514111337556808042, phi_quintC_5911334420514111337556808043, phi_quintC_5911334420514111337556808044,
    phi_quintC_5911334420514111337556808045, phi_quintC_5911334420514111337556808046, phi_quintC_5911334420514111337556808047,
    phi_quintC_5911334420514111337556808048, phi_quintC_5911334420514111337556808049, phi_quintC_5911334420514111337556808050,
    phi_quintC_5911334420514111337556808051, phi_quintC_5911334420514111337556808052, phi_quintC_5911334420514111337556808053,
    phi_quintC_5911334420514111337556808054, phi_quintC_5911334420514111337556808055, phi_quintC_5911334420514111337556808056,
    phi_quintC_5911334420514111337556808057, phi_quintC_5911334420514111337556808058, phi_quintC_5911334420514111337556808059,
    phi_quintC_5911334420514111337556808060, phi_quintC_5911334420514111337556808061, phi_quintC_5911334420514111337556808062,
    phi_quintC_5911334420514111337556808063, phi_quintC_5911334420514111337556808064, phi_quintC_5911334420514111337556808065,
    phi_quintC_5911334420514111337556808066, phi_quintC_5911334420514111337556808067, phi_quintC_5911334420514111337556808068,
    phi_quintC_5911334420514111337556808069, phi_quintC_5911334420514111337556808070, phi_quintC_5911334420514111337556808071,
    phi_quintC_5911334420514111337556808072, phi_quintC_5911334420514111337556808073, phi_quintC_5911334420514111337556808074,
    phi_quintC_5911334420514111337556808075, phi_quintC_5911334420514111337556808076, phi_quintC_5911334420514111337556808077,
    phi_quintC_5911334420514111337556808078, phi_quintC_5911334420514111337556808079, phi_quintC_5911334420514111337556808080,
    phi_quintC_5911334420514111337556808081, phi_quintC_5911334420514111337556808082, phi_quintC_5911334420514111337556808083,
    phi_quintC_5911334420514111337556808084, phi_quintC_5911334420514111337556808085, phi_quintC_5911334420514111337556808086,
    phi_quintC_5911334420514111337556808087, phi_quintC_5911334420514111337556808088, phi_quintC_5911334420514111337556808089,
    phi_quintC_5911334420514111337556808090, phi_quintC_5911334420514111337556808091, phi_quintC_5911334420514111337556808092,
    phi_quintC_5911334420514111337556808093, phi_quintC_5911334420514111337556808094, phi_quintC_5911334420514111337556808095,
    phi_quintC_5911334420514111337556808096, phi_quintC_5911334420514111337556808097]

end TotientTailPeriodKiller
end Erdos249257
