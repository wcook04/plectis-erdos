import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 55P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyFiveBAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyFiveBAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyFiveBAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyFiveBAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyFiveBAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyFiveBAFastPow a n * fiftyFiveBAFastPow a n * a
        else fiftyFiveBAFastPow a n * fiftyFiveBAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyFiveBA_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyFiveBA_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyFiveBA_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyFiveBA_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyFiveBA_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyFiveBA_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyFiveBA_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyFiveBA_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyFiveBA_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyFiveBA_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyFiveBA_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyFiveBA_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyFiveBA_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyFiveBA_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyFiveBA_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyFiveBA_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyFiveBA_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyFiveBA_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyFiveBA_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyFiveBA_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyFiveBA_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyFiveBA_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyFiveBA_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyFiveBA_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyFiveBA_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyFiveBA_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyFiveBA_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyFiveBA_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyFiveBA_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyFiveBA_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyFiveBA_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyFiveBA_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyFiveBA_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyFiveBA_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyFiveBA_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyFiveBA_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyFiveBA_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyFiveBA_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyFiveBA_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyFiveBA_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyFiveBA_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyFiveBA_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyFiveBA_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyFiveBA_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyFiveBA_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyFiveBA_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyFiveBA_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyFiveBA_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftyFiveBA_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyFiveBA_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyFiveBA_257 : Nat.Prime 257 := by norm_num
private theorem prime_fiftyFiveBA_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyFiveBA_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyFiveBA_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyFiveBA_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyFiveBA_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyFiveBA_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftyFiveBA_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyFiveBA_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyFiveBA_317 : Nat.Prime 317 := by norm_num
private theorem prime_fiftyFiveBA_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftyFiveBA_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyFiveBA_349 : Nat.Prime 349 := by norm_num
private theorem prime_fiftyFiveBA_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftyFiveBA_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyFiveBA_401 : Nat.Prime 401 := by norm_num
private theorem prime_fiftyFiveBA_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyFiveBA_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftyFiveBA_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyFiveBA_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftyFiveBA_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftyFiveBA_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftyFiveBA_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftyFiveBA_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyFiveBA_487 : Nat.Prime 487 := by norm_num
private theorem prime_fiftyFiveBA_491 : Nat.Prime 491 := by norm_num
private theorem prime_fiftyFiveBA_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyFiveBA_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyFiveBA_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyFiveBA_547 : Nat.Prime 547 := by norm_num
private theorem prime_fiftyFiveBA_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyFiveBA_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftyFiveBA_571 : Nat.Prime 571 := by norm_num
private theorem prime_fiftyFiveBA_593 : Nat.Prime 593 := by norm_num
private theorem prime_fiftyFiveBA_607 : Nat.Prime 607 := by norm_num
private theorem prime_fiftyFiveBA_613 : Nat.Prime 613 := by norm_num
private theorem prime_fiftyFiveBA_617 : Nat.Prime 617 := by norm_num
private theorem prime_fiftyFiveBA_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftyFiveBA_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftyFiveBA_641 : Nat.Prime 641 := by norm_num
private theorem prime_fiftyFiveBA_643 : Nat.Prime 643 := by norm_num
private theorem prime_fiftyFiveBA_647 : Nat.Prime 647 := by norm_num
private theorem prime_fiftyFiveBA_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftyFiveBA_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyFiveBA_727 : Nat.Prime 727 := by norm_num
private theorem prime_fiftyFiveBA_751 : Nat.Prime 751 := by norm_num
private theorem prime_fiftyFiveBA_757 : Nat.Prime 757 := by norm_num
private theorem prime_fiftyFiveBA_761 : Nat.Prime 761 := by norm_num
private theorem prime_fiftyFiveBA_823 : Nat.Prime 823 := by norm_num
private theorem prime_fiftyFiveBA_827 : Nat.Prime 827 := by norm_num
private theorem prime_fiftyFiveBA_829 : Nat.Prime 829 := by norm_num
private theorem prime_fiftyFiveBA_857 : Nat.Prime 857 := by norm_num
private theorem prime_fiftyFiveBA_877 : Nat.Prime 877 := by norm_num
private theorem prime_fiftyFiveBA_929 : Nat.Prime 929 := by norm_num
private theorem prime_fiftyFiveBA_941 : Nat.Prime 941 := by norm_num
private theorem prime_fiftyFiveBA_953 : Nat.Prime 953 := by norm_num
private theorem prime_fiftyFiveBA_967 : Nat.Prime 967 := by norm_num
private theorem prime_fiftyFiveBA_971 : Nat.Prime 971 := by norm_num
private theorem prime_fiftyFiveBA_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftyFiveBA_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fiftyFiveBA_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fiftyFiveBA_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_fiftyFiveBA_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fiftyFiveBA_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_fiftyFiveBA_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fiftyFiveBA_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fiftyFiveBA_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_fiftyFiveBA_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fiftyFiveBA_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftyFiveBA_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fiftyFiveBA_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_fiftyFiveBA_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fiftyFiveBA_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fiftyFiveBA_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_fiftyFiveBA_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_fiftyFiveBA_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_fiftyFiveBA_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_fiftyFiveBA_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_fiftyFiveBA_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_fiftyFiveBA_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_fiftyFiveBA_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fiftyFiveBA_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_fiftyFiveBA_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_fiftyFiveBA_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_fiftyFiveBA_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fiftyFiveBA_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fiftyFiveBA_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_fiftyFiveBA_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_fiftyFiveBA_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_fiftyFiveBA_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_fiftyFiveBA_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_fiftyFiveBA_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_fiftyFiveBA_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_fiftyFiveBA_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_fiftyFiveBA_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_fiftyFiveBA_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_fiftyFiveBA_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_fiftyFiveBA_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_fiftyFiveBA_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_fiftyFiveBA_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_fiftyFiveBA_3919 : Nat.Prime 3919 := by norm_num
private theorem prime_fiftyFiveBA_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_fiftyFiveBA_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_fiftyFiveBA_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_fiftyFiveBA_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_fiftyFiveBA_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_fiftyFiveBA_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_fiftyFiveBA_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_fiftyFiveBA_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_fiftyFiveBA_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_fiftyFiveBA_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyFiveBA_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_fiftyFiveBA_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_fiftyFiveBA_5351 : Nat.Prime 5351 := by norm_num
private theorem prime_fiftyFiveBA_5431 : Nat.Prime 5431 := by norm_num
private theorem prime_fiftyFiveBA_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_fiftyFiveBA_5471 : Nat.Prime 5471 := by norm_num
private theorem prime_fiftyFiveBA_5521 : Nat.Prime 5521 := by norm_num
private theorem prime_fiftyFiveBA_5689 : Nat.Prime 5689 := by norm_num
private theorem prime_fiftyFiveBA_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_fiftyFiveBA_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_fiftyFiveBA_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fiftyFiveBA_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fiftyFiveBA_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_fiftyFiveBA_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_fiftyFiveBA_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_fiftyFiveBA_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_fiftyFiveBA_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_fiftyFiveBA_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_fiftyFiveBA_7187 : Nat.Prime 7187 := by norm_num
private theorem prime_fiftyFiveBA_7219 : Nat.Prime 7219 := by norm_num
private theorem prime_fiftyFiveBA_7253 : Nat.Prime 7253 := by norm_num
private theorem prime_fiftyFiveBA_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_fiftyFiveBA_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_fiftyFiveBA_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_fiftyFiveBA_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_fiftyFiveBA_9811 : Nat.Prime 9811 := by norm_num
private theorem prime_fiftyFiveBA_9839 : Nat.Prime 9839 := by norm_num
private theorem prime_fiftyFiveBA_10597 : Nat.Prime 10597 := by norm_num
private theorem prime_fiftyFiveBA_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fiftyFiveBA_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_fiftyFiveBA_10859 : Nat.Prime 10859 := by norm_num
private theorem prime_fiftyFiveBA_11047 : Nat.Prime 11047 := by norm_num
private theorem prime_fiftyFiveBA_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_fiftyFiveBA_11447 : Nat.Prime 11447 := by norm_num
private theorem prime_fiftyFiveBA_11801 : Nat.Prime 11801 := by norm_num
private theorem prime_fiftyFiveBA_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_fiftyFiveBA_13109 : Nat.Prime 13109 := by norm_num
private theorem prime_fiftyFiveBA_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_fiftyFiveBA_15439 : Nat.Prime 15439 := by norm_num
private theorem prime_fiftyFiveBA_16447 : Nat.Prime 16447 := by norm_num
private theorem prime_fiftyFiveBA_17291 : Nat.Prime 17291 := by norm_num
private theorem prime_fiftyFiveBA_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_fiftyFiveBA_18217 : Nat.Prime 18217 := by norm_num
private theorem prime_fiftyFiveBA_19157 : Nat.Prime 19157 := by norm_num
private theorem prime_fiftyFiveBA_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_fiftyFiveBA_19963 : Nat.Prime 19963 := by norm_num
private theorem prime_fiftyFiveBA_20753 : Nat.Prime 20753 := by norm_num
private theorem prime_fiftyFiveBA_22483 : Nat.Prime 22483 := by norm_num
private theorem prime_fiftyFiveBA_22511 : Nat.Prime 22511 := by norm_num
private theorem prime_fiftyFiveBA_23099 : Nat.Prime 23099 := by norm_num
private theorem prime_fiftyFiveBA_23417 : Nat.Prime 23417 := by norm_num
private theorem prime_fiftyFiveBA_25439 : Nat.Prime 25439 := by norm_num
private theorem prime_fiftyFiveBA_25667 : Nat.Prime 25667 := by norm_num
private theorem prime_fiftyFiveBA_25969 : Nat.Prime 25969 := by norm_num
private theorem prime_fiftyFiveBA_26947 : Nat.Prime 26947 := by norm_num
private theorem prime_fiftyFiveBA_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_fiftyFiveBA_27361 : Nat.Prime 27361 := by norm_num
private theorem prime_fiftyFiveBA_27481 : Nat.Prime 27481 := by norm_num
private theorem prime_fiftyFiveBA_27883 : Nat.Prime 27883 := by norm_num
private theorem prime_fiftyFiveBA_28663 : Nat.Prime 28663 := by norm_num
private theorem prime_fiftyFiveBA_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_fiftyFiveBA_28703 : Nat.Prime 28703 := by norm_num
private theorem prime_fiftyFiveBA_31159 : Nat.Prime 31159 := by norm_num
private theorem prime_fiftyFiveBA_32531 : Nat.Prime 32531 := by norm_num
private theorem prime_fiftyFiveBA_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_fiftyFiveBA_32869 : Nat.Prime 32869 := by norm_num
private theorem prime_fiftyFiveBA_33347 : Nat.Prime 33347 := by norm_num
private theorem prime_fiftyFiveBA_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyFiveBA_35569 : Nat.Prime 35569 := by norm_num
private theorem prime_fiftyFiveBA_36467 : Nat.Prime 36467 := by norm_num
private theorem prime_fiftyFiveBA_36541 : Nat.Prime 36541 := by norm_num
private theorem prime_fiftyFiveBA_36691 : Nat.Prime 36691 := by norm_num
private theorem prime_fiftyFiveBA_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_fiftyFiveBA_37967 : Nat.Prime 37967 := by norm_num
private theorem prime_fiftyFiveBA_39113 : Nat.Prime 39113 := by norm_num
private theorem prime_fiftyFiveBA_47297 : Nat.Prime 47297 := by norm_num
private theorem prime_fiftyFiveBA_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_fiftyFiveBA_48973 : Nat.Prime 48973 := by norm_num
private theorem prime_fiftyFiveBA_53923 : Nat.Prime 53923 := by norm_num
private theorem prime_fiftyFiveBA_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_fiftyFiveBA_54521 : Nat.Prime 54521 := by norm_num
private theorem prime_fiftyFiveBA_55663 : Nat.Prime 55663 := by norm_num
private theorem prime_fiftyFiveBA_57793 : Nat.Prime 57793 := by norm_num
private theorem prime_fiftyFiveBA_59183 : Nat.Prime 59183 := by norm_num
private theorem prime_fiftyFiveBA_59387 : Nat.Prime 59387 := by norm_num
private theorem prime_fiftyFiveBA_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyFiveBA_62549 : Nat.Prime 62549 := by norm_num
private theorem prime_fiftyFiveBA_65269 : Nat.Prime 65269 := by norm_num
private theorem prime_fiftyFiveBA_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_fiftyFiveBA_68141 : Nat.Prime 68141 := by norm_num
private theorem prime_fiftyFiveBA_71699 : Nat.Prime 71699 := by norm_num
private theorem prime_fiftyFiveBA_73751 : Nat.Prime 73751 := by norm_num
private theorem prime_fiftyFiveBA_74687 : Nat.Prime 74687 := by norm_num
private theorem prime_fiftyFiveBA_74717 : Nat.Prime 74717 := by norm_num
private theorem prime_fiftyFiveBA_76123 : Nat.Prime 76123 := by norm_num
private theorem prime_fiftyFiveBA_77267 : Nat.Prime 77267 := by norm_num
private theorem prime_fiftyFiveBA_83843 : Nat.Prime 83843 := by norm_num
private theorem prime_fiftyFiveBA_85193 : Nat.Prime 85193 := by norm_num
private theorem prime_fiftyFiveBA_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_fiftyFiveBA_85931 : Nat.Prime 85931 := by norm_num
private theorem prime_fiftyFiveBA_86729 : Nat.Prime 86729 := by norm_num
private theorem prime_fiftyFiveBA_87541 : Nat.Prime 87541 := by norm_num
private theorem prime_fiftyFiveBA_92639 : Nat.Prime 92639 := by norm_num
private theorem prime_fiftyFiveBA_95101 : Nat.Prime 95101 := by norm_num
private theorem prime_fiftyFiveBA_97651 : Nat.Prime 97651 := by norm_num
private theorem prime_fiftyFiveBA_99133 : Nat.Prime 99133 := by norm_num
private theorem prime_fiftyFiveBA_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_fiftyFiveBA_102539 : Nat.Prime 102539 := by norm_num
private theorem prime_fiftyFiveBA_104053 : Nat.Prime 104053 := by norm_num
private theorem prime_fiftyFiveBA_108991 : Nat.Prime 108991 := by norm_num
private theorem prime_fiftyFiveBA_109097 : Nat.Prime 109097 := by norm_num
private theorem prime_fiftyFiveBA_113017 : Nat.Prime 113017 := by norm_num
private theorem prime_fiftyFiveBA_132113 : Nat.Prime 132113 := by norm_num
private theorem prime_fiftyFiveBA_139187 : Nat.Prime 139187 := by norm_num
private theorem prime_fiftyFiveBA_141707 : Nat.Prime 141707 := by norm_num
private theorem prime_fiftyFiveBA_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_fiftyFiveBA_144889 : Nat.Prime 144889 := by norm_num
private theorem prime_fiftyFiveBA_149057 : Nat.Prime 149057 := by norm_num
private theorem prime_fiftyFiveBA_154807 : Nat.Prime 154807 := by norm_num
private theorem prime_fiftyFiveBA_185483 : Nat.Prime 185483 := by norm_num
private theorem prime_fiftyFiveBA_186227 : Nat.Prime 186227 := by norm_num
private theorem prime_fiftyFiveBA_196429 : Nat.Prime 196429 := by norm_num
private theorem prime_fiftyFiveBA_198251 : Nat.Prime 198251 := by norm_num
private theorem prime_fiftyFiveBA_201473 : Nat.Prime 201473 := by norm_num
private theorem prime_fiftyFiveBA_222419 : Nat.Prime 222419 := by norm_num
private theorem prime_fiftyFiveBA_277247 : Nat.Prime 277247 := by norm_num
private theorem prime_fiftyFiveBA_313127 : Nat.Prime 313127 := by norm_num
private theorem prime_fiftyFiveBA_314989 : Nat.Prime 314989 := by norm_num
private theorem prime_fiftyFiveBA_353677 : Nat.Prime 353677 := by norm_num
private theorem prime_fiftyFiveBA_368791 : Nat.Prime 368791 := by norm_num
private theorem prime_fiftyFiveBA_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_fiftyFiveBA_386839 : Nat.Prime 386839 := by norm_num
private theorem prime_fiftyFiveBA_405407 : Nat.Prime 405407 := by norm_num
private theorem prime_fiftyFiveBA_414709 : Nat.Prime 414709 := by norm_num
private theorem prime_fiftyFiveBA_417019 : Nat.Prime 417019 := by norm_num
private theorem prime_fiftyFiveBA_426779 : Nat.Prime 426779 := by norm_num
private theorem prime_fiftyFiveBA_434563 : Nat.Prime 434563 := by norm_num
private theorem prime_fiftyFiveBA_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_fiftyFiveBA_514793 : Nat.Prime 514793 := by norm_num
private theorem prime_fiftyFiveBA_518207 : Nat.Prime 518207 := by norm_num
private theorem prime_fiftyFiveBA_531857 : Nat.Prime 531857 := by norm_num
private theorem prime_fiftyFiveBA_533077 : Nat.Prime 533077 := by norm_num
private theorem prime_fiftyFiveBA_541727 : Nat.Prime 541727 := by norm_num
private theorem prime_fiftyFiveBA_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_fiftyFiveBA_570527 : Nat.Prime 570527 := by norm_num
private theorem prime_fiftyFiveBA_571789 : Nat.Prime 571789 := by norm_num
private theorem prime_fiftyFiveBA_581351 : Nat.Prime 581351 := by norm_num
private theorem prime_fiftyFiveBA_628877 : Nat.Prime 628877 := by norm_num
private theorem prime_fiftyFiveBA_630151 : Nat.Prime 630151 := by norm_num
private theorem prime_fiftyFiveBA_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_fiftyFiveBA_659917 : Nat.Prime 659917 := by norm_num
private theorem prime_fiftyFiveBA_705277 : Nat.Prime 705277 := by norm_num
private theorem prime_fiftyFiveBA_747277 : Nat.Prime 747277 := by norm_num
private theorem prime_fiftyFiveBA_810913 : Nat.Prime 810913 := by norm_num
private theorem prime_fiftyFiveBA_834527 : Nat.Prime 834527 := by norm_num
private theorem prime_fiftyFiveBA_847031 : Nat.Prime 847031 := by norm_num
private theorem prime_fiftyFiveBA_850613 : Nat.Prime 850613 := by norm_num
private theorem prime_fiftyFiveBA_895529 : Nat.Prime 895529 := by norm_num
private theorem prime_fiftyFiveBA_901441 : Nat.Prime 901441 := by norm_num
private theorem prime_fiftyFiveBA_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_fiftyFiveBA_906673 : Nat.Prime 906673 := by norm_num
private theorem prime_fiftyFiveBA_928163 : Nat.Prime 928163 := by norm_num
private theorem prime_fiftyFiveBA_940573 : Nat.Prime 940573 := by norm_num
private theorem prime_fiftyFiveBA_961861 : Nat.Prime 961861 := by norm_num
private theorem prime_fiftyFiveBA_1127981 : Nat.Prime 1127981 := by norm_num
private theorem prime_fiftyFiveBA_1231171 : Nat.Prime 1231171 := by norm_num
private theorem prime_fiftyFiveBA_1281463 : Nat.Prime 1281463 := by norm_num
private theorem prime_fiftyFiveBA_1381489 : Nat.Prime 1381489 := by norm_num
private theorem prime_fiftyFiveBA_1406039 : Nat.Prime 1406039 := by norm_num
private theorem prime_fiftyFiveBA_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_fiftyFiveBA_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_fiftyFiveBA_1602427 : Nat.Prime 1602427 := by norm_num
private theorem prime_fiftyFiveBA_1603669 : Nat.Prime 1603669 := by norm_num
private theorem prime_fiftyFiveBA_1650287 : Nat.Prime 1650287 := by norm_num
private theorem prime_fiftyFiveBA_1698449 : Nat.Prime 1698449 := by norm_num
private theorem prime_fiftyFiveBA_1880839 : Nat.Prime 1880839 := by norm_num
private theorem prime_fiftyFiveBA_1883407 : Nat.Prime 1883407 := by norm_num
private theorem prime_fiftyFiveBA_1899647 : Nat.Prime 1899647 := by norm_num
private theorem prime_fiftyFiveBA_2091139 : Nat.Prime 2091139 := by norm_num
private theorem prime_fiftyFiveBA_2104699 : Nat.Prime 2104699 := by norm_num
private theorem prime_fiftyFiveBA_2128781 : Nat.Prime 2128781 := by norm_num
private theorem prime_fiftyFiveBA_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_fiftyFiveBA_2249981 : Nat.Prime 2249981 := by norm_num
private theorem prime_fiftyFiveBA_2375111 : Nat.Prime 2375111 := by norm_num
private theorem prime_fiftyFiveBA_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_fiftyFiveBA_2567447 : Nat.Prime 2567447 := by norm_num
private theorem prime_fiftyFiveBA_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_fiftyFiveBA_2800583 : Nat.Prime 2800583 := by norm_num
private theorem prime_fiftyFiveBA_2816909 : Nat.Prime 2816909 := by norm_num
private theorem prime_fiftyFiveBA_2945933 : Nat.Prime 2945933 := by norm_num
private theorem prime_fiftyFiveBA_3033757 : Nat.Prime 3033757 := by norm_num
private theorem prime_fiftyFiveBA_3072847 : Nat.Prime 3072847 := by norm_num
private theorem prime_fiftyFiveBA_3089941 : Nat.Prime 3089941 := by norm_num
private theorem prime_fiftyFiveBA_3301777 : Nat.Prime 3301777 := by norm_num
private theorem prime_fiftyFiveBA_3303353 : Nat.Prime 3303353 := by norm_num
private theorem prime_fiftyFiveBA_3344557 : Nat.Prime 3344557 := by norm_num
private theorem prime_fiftyFiveBA_3374797 : Nat.Prime 3374797 := by norm_num
private theorem prime_fiftyFiveBA_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_fiftyFiveBA_3446959 : Nat.Prime 3446959 := by norm_num
private theorem prime_fiftyFiveBA_3454249 : Nat.Prime 3454249 := by norm_num
private theorem prime_fiftyFiveBA_3637709 : Nat.Prime 3637709 := by norm_num
private theorem prime_fiftyFiveBA_3707213 : Nat.Prime 3707213 := by norm_num
private theorem prime_fiftyFiveBA_3780509 : Nat.Prime 3780509 := by norm_num
private theorem prime_fiftyFiveBA_3925177 : Nat.Prime 3925177 := by norm_num
private theorem prime_fiftyFiveBA_3993751 : Nat.Prime 3993751 := by norm_num
private theorem prime_fiftyFiveBA_4075433 : Nat.Prime 4075433 := by norm_num
private theorem prime_fiftyFiveBA_4239269 : Nat.Prime 4239269 := by norm_num
private theorem prime_fiftyFiveBA_4272601 : Nat.Prime 4272601 := by norm_num
private theorem prime_fiftyFiveBA_4842707 : Nat.Prime 4842707 := by norm_num
private theorem prime_fiftyFiveBA_5225593 : Nat.Prime 5225593 := by norm_num
private theorem prime_fiftyFiveBA_5253623 : Nat.Prime 5253623 := by norm_num
private theorem prime_fiftyFiveBA_5426387 : Nat.Prime 5426387 := by norm_num
private theorem prime_fiftyFiveBA_5458489 : Nat.Prime 5458489 := by norm_num
private theorem prime_fiftyFiveBA_5811937 : Nat.Prime 5811937 := by norm_num
private theorem prime_fiftyFiveBA_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyFiveBA_7459093 : Nat.Prime 7459093 := by norm_num
private theorem prime_fiftyFiveBA_7958407 : Nat.Prime 7958407 := by norm_num
private theorem prime_fiftyFiveBA_8316337 : Nat.Prime 8316337 := by norm_num
private theorem prime_fiftyFiveBA_8917991 : Nat.Prime 8917991 := by norm_num
private theorem prime_fiftyFiveBA_9047041 : Nat.Prime 9047041 := by norm_num
private theorem prime_fiftyFiveBA_9126011 : Nat.Prime 9126011 := by norm_num
private theorem prime_fiftyFiveBA_9392503 : Nat.Prime 9392503 := by norm_num
private theorem prime_fiftyFiveBA_9599189 : Nat.Prime 9599189 := by norm_num
private theorem prime_fiftyFiveBA_9783821 : Nat.Prime 9783821 := by norm_num
private theorem prime_fiftyFiveBA_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_fiftyFiveBA_10069603 : Nat.Prime 10069603 := by norm_num
private theorem prime_fiftyFiveBA_10728337 : Nat.Prime 10728337 := by norm_num
private theorem prime_fiftyFiveBA_11218483 : Nat.Prime 11218483 := by norm_num
private theorem prime_fiftyFiveBA_11233337 : Nat.Prime 11233337 := by norm_num
private theorem prime_fiftyFiveBA_11503777 : Nat.Prime 11503777 := by norm_num
private theorem prime_fiftyFiveBA_11540831 : Nat.Prime 11540831 := by norm_num
private theorem prime_fiftyFiveBA_11748679 : Nat.Prime 11748679 := by norm_num
private theorem prime_fiftyFiveBA_12598393 : Nat.Prime 12598393 := by norm_num
private theorem prime_fiftyFiveBA_12658649 : Nat.Prime 12658649 := by norm_num
private theorem prime_fiftyFiveBA_12876961 : Nat.Prime 12876961 := by norm_num
private theorem prime_fiftyFiveBA_13084949 : Nat.Prime 13084949 := by norm_num
private theorem prime_fiftyFiveBA_13100239 : Nat.Prime 13100239 := by norm_num
private theorem prime_fiftyFiveBA_13130393 : Nat.Prime 13130393 := by norm_num
private theorem prime_fiftyFiveBA_13335683 : Nat.Prime 13335683 := by norm_num
private theorem prime_fiftyFiveBA_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_fiftyFiveBA_15018779 : Nat.Prime 15018779 := by norm_num
private theorem prime_fiftyFiveBA_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_fiftyFiveBA_16491773 : Nat.Prime 16491773 := by norm_num
private theorem prime_fiftyFiveBA_17198551 : Nat.Prime 17198551 := by norm_num
private theorem prime_fiftyFiveBA_17330239 : Nat.Prime 17330239 := by norm_num
private theorem prime_fiftyFiveBA_18126877 : Nat.Prime 18126877 := by norm_num
private theorem prime_fiftyFiveBA_18241513 : Nat.Prime 18241513 := by norm_num
private theorem prime_fiftyFiveBA_19804481 : Nat.Prime 19804481 := by norm_num
private theorem prime_fiftyFiveBA_21160721 : Nat.Prime 21160721 := by norm_num
private theorem prime_fiftyFiveBA_21768611 : Nat.Prime 21768611 := by norm_num
private theorem prime_fiftyFiveBA_23790577 : Nat.Prime 23790577 := by norm_num
private theorem prime_fiftyFiveBA_25574243 : Nat.Prime 25574243 := by norm_num
private theorem prime_fiftyFiveBA_25824109 : Nat.Prime 25824109 := by norm_num
private theorem prime_fiftyFiveBA_29602789 : Nat.Prime 29602789 := by norm_num
private theorem prime_fiftyFiveBA_31833629 : Nat.Prime 31833629 := by
  apply lucas_primality 31833629 (2 : ZMod 31833629)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7958407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7958407, 1)] : List FactorBlock).map factorBlockValue).prod) = 31833629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7958407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31833629) ^ 15916814 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31833629) ^ 4 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_32958059 : Nat.Prime 32958059 := by
  apply lucas_primality 32958059 (6 : ZMod 32958059)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 2), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 2), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 32958059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_71
      · exact prime_fiftyFiveBA_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 32958059) ^ 16479029 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 32958059) ^ 4708294 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 32958059) ^ 464198 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 32958059) ^ 70574 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_33968981 : Nat.Prime 33968981 := by
  apply lucas_primality 33968981 (2 : ZMod 33968981)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1698449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1698449, 1)] : List FactorBlock).map factorBlockValue).prod) = 33968981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_1698449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33968981) ^ 16984490 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33968981) ^ 6793796 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33968981) ^ 20 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_34091807 : Nat.Prime 34091807 := by
  apply lucas_primality 34091807 (5 : ZMod 34091807)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod) = 34091807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34091807) ^ 17045903 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 4870258 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 383054 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 1246 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_34231621 : Nat.Prime 34231621 := by
  apply lucas_primality 34231621 (10 : ZMod 34231621)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (570527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (570527, 1)] : List FactorBlock).map factorBlockValue).prod) = 34231621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_570527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 34231621) ^ 17115810 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34231621) ^ 11410540 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34231621) ^ 6846324 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34231621) ^ 60 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_34417993 : Nat.Prime 34417993 := by
  apply lucas_primality 34417993 (5 : ZMod 34417993)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (37, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (37, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 34417993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34417993) ^ 17208996 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34417993) ^ 11472664 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34417993) ^ 4916856 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34417993) ^ 930216 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 34417993) ^ 304584 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_41242609 : Nat.Prime 41242609 := by
  apply lucas_primality 41242609 (13 : ZMod 41242609)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 2), (263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 2), (263, 1)] : List FactorBlock).map factorBlockValue).prod) = 41242609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 41242609) ^ 20621304 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 41242609) ^ 13747536 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 41242609) ^ 3749328 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 41242609) ^ 156816 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_54083423 : Nat.Prime 54083423 := by
  apply lucas_primality 54083423 (5 : ZMod 54083423)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (628877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (628877, 1)] : List FactorBlock).map factorBlockValue).prod) = 54083423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_628877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 54083423) ^ 27041711 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 54083423) ^ 1257754 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 54083423) ^ 86 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_54756067 : Nat.Prime 54756067 := by
  apply lucas_primality 54756067 (3 : ZMod 54756067)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9126011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9126011, 1)] : List FactorBlock).map factorBlockValue).prod) = 54756067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_9126011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54756067) ^ 27378033 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54756067) ^ 18252022 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54756067) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_55379759 : Nat.Prime 55379759 := by
  apply lucas_primality 55379759 (7 : ZMod 55379759)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 55379759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_83
      · exact prime_fiftyFiveBA_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55379759) ^ 27689879 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 7911394 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 667226 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 1162 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_60308257 : Nat.Prime 60308257 := by
  apply lucas_primality 60308257 (5 : ZMod 60308257)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 60308257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_643
      · exact prime_fiftyFiveBA_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60308257) ^ 30154128 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 20102752 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 93792 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 61728 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_62762281 : Nat.Prime 62762281 := by
  apply lucas_primality 62762281 (11 : ZMod 62762281)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (74717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (74717, 1)] : List FactorBlock).map factorBlockValue).prod) = 62762281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_74717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 62762281) ^ 31381140 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 62762281) ^ 20920760 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 62762281) ^ 12552456 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 62762281) ^ 8966040 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 62762281) ^ 840 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_67937963 : Nat.Prime 67937963 := by
  apply lucas_primality 67937963 (2 : ZMod 67937963)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33968981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33968981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67937963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_33968981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 67937963) ^ 33968981 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67937963) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_68509517 : Nat.Prime 68509517 := by
  apply lucas_primality 68509517 (2 : ZMod 68509517)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (901441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (901441, 1)] : List FactorBlock).map factorBlockValue).prod) = 68509517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_901441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68509517) ^ 34254758 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 68509517) ^ 3605764 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 68509517) ^ 76 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_69981487 : Nat.Prime 69981487 := by
  apply lucas_primality 69981487 (6 : ZMod 69981487)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (101, 1), (6793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (101, 1), (6793, 1)] : List FactorBlock).map factorBlockValue).prod) = 69981487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_101
      · exact prime_fiftyFiveBA_6793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 69981487) ^ 34990743 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 69981487) ^ 23327162 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 69981487) ^ 4116558 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 69981487) ^ 692886 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 69981487) ^ 10302 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_72966053 : Nat.Prime 72966053 := by
  apply lucas_primality 72966053 (2 : ZMod 72966053)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18241513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18241513, 1)] : List FactorBlock).map factorBlockValue).prod) = 72966053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_18241513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72966053) ^ 36483026 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72966053) ^ 4 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_74144261 : Nat.Prime 74144261 := by
  apply lucas_primality 74144261 (2 : ZMod 74144261)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod) = 74144261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_3707213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74144261) ^ 37072130 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 14828852 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 20 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_75111599 : Nat.Prime 75111599 := by
  apply lucas_primality 75111599 (17 : ZMod 75111599)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod) = 75111599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_73
      · exact prime_fiftyFiveBA_27077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 75111599) ^ 37555799 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 3953242 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 1028926 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 2774 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_78782359 : Nat.Prime 78782359 := by
  apply lucas_primality 78782359 (3 : ZMod 78782359)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13130393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13130393, 1)] : List FactorBlock).map factorBlockValue).prod) = 78782359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13130393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78782359) ^ 39391179 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 78782359) ^ 26260786 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 78782359) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_80247329 : Nat.Prime 80247329 := by
  apply lucas_primality 80247329 (3 : ZMod 80247329)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (101, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (101, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) = 80247329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_101
      · exact prime_fiftyFiveBA_3547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 80247329) ^ 40123664 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 80247329) ^ 11463904 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 80247329) ^ 794528 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 80247329) ^ 22624 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_80744533 : Nat.Prime 80744533 := by
  apply lucas_primality 80744533 (6 : ZMod 80744533)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 80744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_151
      · exact prime_fiftyFiveBA_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 80744533) ^ 40372266 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 26914844 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 7340412 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 534732 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 19932 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_82478657 : Nat.Prime 82478657 := by
  apply lucas_primality 82478657 (5 : ZMod 82478657)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (99133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (99133, 1)] : List FactorBlock).map factorBlockValue).prod) = 82478657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_99133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 82478657) ^ 41239328 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 82478657) ^ 6344512 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 82478657) ^ 832 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_83676301 : Nat.Prime 83676301 := by
  apply lucas_primality 83676301 (6 : ZMod 83676301)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 1), (67, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 1), (67, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 83676301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 83676301) ^ 41838150 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83676301) ^ 27892100 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83676301) ^ 16735260 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83676301) ^ 3638100 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83676301) ^ 1248900 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83676301) ^ 462300 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_93644869 : Nat.Prime 93644869 := by
  apply lucas_primality 93644869 (2 : ZMod 93644869)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (47, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (47, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) = 93644869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_7219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93644869) ^ 46822434 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93644869) ^ 31214956 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93644869) ^ 4071516 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93644869) ^ 1992444 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93644869) ^ 12972 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_98695889 : Nat.Prime 98695889 := by
  apply lucas_primality 98695889 (3 : ZMod 98695889)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod) = 98695889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_967
      · exact prime_fiftyFiveBA_6379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98695889) ^ 49347944 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 102064 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 15472 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_100696031 : Nat.Prime 100696031 := by
  apply lucas_primality 100696031 (7 : ZMod 100696031)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10069603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10069603, 1)] : List FactorBlock).map factorBlockValue).prod) = 100696031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_10069603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100696031) ^ 50348015 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 100696031) ^ 20139206 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 100696031) ^ 10 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_112850341 : Nat.Prime 112850341 := by
  apply lucas_primality 112850341 (6 : ZMod 112850341)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1880839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1880839, 1)] : List FactorBlock).map factorBlockValue).prod) = 112850341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_1880839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 112850341) ^ 56425170 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 112850341) ^ 37616780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 112850341) ^ 22570068 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 112850341) ^ 60 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_115677223 : Nat.Prime 115677223 := by
  apply lucas_primality 115677223 (3 : ZMod 115677223)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (929, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (929, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 115677223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_929
      · exact prime_fiftyFiveBA_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115677223) ^ 57838611 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 115677223) ^ 38559074 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 115677223) ^ 124518 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 115677223) ^ 5574 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_118826887 : Nat.Prime 118826887 := by
  apply lucas_primality 118826887 (6 : ZMod 118826887)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod) = 118826887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_19804481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 118826887) ^ 59413443 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 39608962 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_128144927 : Nat.Prime 128144927 := by
  apply lucas_primality 128144927 (5 : ZMod 128144927)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (41, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (41, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 128144927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 128144927) ^ 64072463 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 128144927) ^ 18306418 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 128144927) ^ 9857302 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 128144927) ^ 3125486 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 128144927) ^ 97006 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_134406001 : Nat.Prime 134406001 := by
  apply lucas_primality 134406001 (17 : ZMod 134406001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 134406001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 134406001) ^ 67203000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 44802000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 26881200 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 7074000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 1026000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_174243361 : Nat.Prime 174243361 := by
  apply lucas_primality 174243361 (11 : ZMod 174243361)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (37, 1), (9811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (37, 1), (9811, 1)] : List FactorBlock).map factorBlockValue).prod) = 174243361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_9811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 174243361) ^ 87121680 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243361) ^ 58081120 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243361) ^ 34848672 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243361) ^ 4709280 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 174243361) ^ 17760 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_188131817 : Nat.Prime 188131817 := by
  apply lucas_primality 188131817 (3 : ZMod 188131817)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod) = 188131817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_810913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 188131817) ^ 94065908 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 6487304 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 232 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_189730477 : Nat.Prime 189730477 := by
  apply lucas_primality 189730477 (11 : ZMod 189730477)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (405407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (405407, 1)] : List FactorBlock).map factorBlockValue).prod) = 189730477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_405407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 189730477) ^ 94865238 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 189730477) ^ 63243492 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 189730477) ^ 14594652 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 189730477) ^ 468 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_213717929 : Nat.Prime 213717929 := by
  apply lucas_primality 213717929 (3 : ZMod 213717929)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (1406039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (1406039, 1)] : List FactorBlock).map factorBlockValue).prod) = 213717929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_1406039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213717929) ^ 106858964 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 213717929) ^ 11248312 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 213717929) ^ 152 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_217917283 : Nat.Prime 217917283 := by
  apply lucas_primality 217917283 (2 : ZMod 217917283)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (3301777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (3301777, 1)] : List FactorBlock).map factorBlockValue).prod) = 217917283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_3301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 217917283) ^ 108958641 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 217917283) ^ 72639094 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 217917283) ^ 19810662 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 217917283) ^ 66 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_219091589 : Nat.Prime 219091589 := by
  apply lucas_primality 219091589 (2 : ZMod 219091589)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6389, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6389, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod) = 219091589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_6389
      · exact prime_fiftyFiveBA_8573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219091589) ^ 109545794 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 219091589) ^ 34292 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 219091589) ^ 25556 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_229518851 : Nat.Prime 229518851 := by
  apply lucas_primality 229518851 (2 : ZMod 229518851)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 2), (59, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 2), (59, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 229518851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 229518851) ^ 114759425 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 229518851) ^ 45903770 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 229518851) ^ 20865350 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 229518851) ^ 3890150 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 229518851) ^ 356950 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_240209789 : Nat.Prime 240209789 := by
  apply lucas_primality 240209789 (2 : ZMod 240209789)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (659917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (659917, 1)] : List FactorBlock).map factorBlockValue).prod) = 240209789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_659917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240209789) ^ 120104894 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240209789) ^ 34315684 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240209789) ^ 18477676 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240209789) ^ 364 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_249532343 : Nat.Prime 249532343 := by
  apply lucas_primality 249532343 (5 : ZMod 249532343)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1831, 1), (68141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1831, 1), (68141, 1)] : List FactorBlock).map factorBlockValue).prod) = 249532343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_1831
      · exact prime_fiftyFiveBA_68141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 249532343) ^ 124766171 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 249532343) ^ 136282 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 249532343) ^ 3662 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_267094367 : Nat.Prime 267094367 := by
  apply lucas_primality 267094367 (5 : ZMod 267094367)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (157, 1), (11047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (157, 1), (11047, 1)] : List FactorBlock).map factorBlockValue).prod) = 267094367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_157
      · exact prime_fiftyFiveBA_11047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 267094367) ^ 133547183 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 267094367) ^ 38156338 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 267094367) ^ 24281306 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 267094367) ^ 1701238 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 267094367) ^ 24178 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_272794601 : Nat.Prime 272794601 := by
  apply lucas_primality 272794601 (6 : ZMod 272794601)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (239, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (239, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 272794601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_239
      · exact prime_fiftyFiveBA_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 272794601) ^ 136397300 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 272794601) ^ 54558920 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 272794601) ^ 20984200 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 272794601) ^ 1141400 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 272794601) ^ 621400 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_279077861 : Nat.Prime 279077861 := by
  apply lucas_primality 279077861 (2 : ZMod 279077861)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (53, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (53, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod) = 279077861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_11447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 279077861) ^ 139538930 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 279077861) ^ 55815572 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 279077861) ^ 12133820 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 279077861) ^ 5265620 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 279077861) ^ 24380 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_279180007 : Nat.Prime 279180007 := by
  apply lucas_primality 279180007 (3 : ZMod 279180007)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod) = 279180007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 279180007) ^ 139590003 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 93060002 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 39882858 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3136854 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3738 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_307588711 : Nat.Prime 307588711 := by
  apply lucas_primality 307588711 (3 : ZMod 307588711)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (71699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (71699, 1)] : List FactorBlock).map factorBlockValue).prod) = 307588711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_71699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 307588711) ^ 153794355 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 307588711) ^ 102529570 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 307588711) ^ 61517742 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 307588711) ^ 27962610 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 307588711) ^ 23660670 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 307588711) ^ 4290 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_316376989 : Nat.Prime 316376989 := by
  apply lucas_primality 316376989 (2 : ZMod 316376989)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (79, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (79, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) = 316376989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_61
      · exact prime_fiftyFiveBA_79
      · exact prime_fiftyFiveBA_5471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 316376989) ^ 158188494 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 316376989) ^ 105458996 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 316376989) ^ 5186508 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 316376989) ^ 4004772 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 316376989) ^ 57828 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_400329661 : Nat.Prime 400329661 := by
  apply lucas_primality 400329661 (6 : ZMod 400329661)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (101, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (101, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 400329661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_101
      · exact prime_fiftyFiveBA_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 400329661) ^ 200164830 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 400329661) ^ 133443220 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 400329661) ^ 80065932 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 400329661) ^ 12913860 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 400329661) ^ 3963660 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 400329661) ^ 187860 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_427435859 : Nat.Prime 427435859 := by
  apply lucas_primality 427435859 (2 : ZMod 427435859)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (213717929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (213717929, 1)] : List FactorBlock).map factorBlockValue).prod) = 427435859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_213717929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 427435859) ^ 213717929 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 427435859) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_552015643 : Nat.Prime 552015643 := by
  apply lucas_primality 552015643 (2 : ZMod 552015643)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (661, 1), (139187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (661, 1), (139187, 1)] : List FactorBlock).map factorBlockValue).prod) = 552015643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_661
      · exact prime_fiftyFiveBA_139187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 552015643) ^ 276007821 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 552015643) ^ 184005214 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 552015643) ^ 835122 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 552015643) ^ 3966 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_553087763 : Nat.Prime 553087763 := by
  apply lucas_primality 553087763 (2 : ZMod 553087763)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (463, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (463, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) = 553087763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_463
      · exact prime_fiftyFiveBA_25969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 553087763) ^ 276543881 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 553087763) ^ 24047294 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 553087763) ^ 1194574 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 553087763) ^ 21298 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_644034299 : Nat.Prime 644034299 := by
  apply lucas_primality 644034299 (2 : ZMod 644034299)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (3539, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (3539, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) = 644034299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_3539
      · exact prime_fiftyFiveBA_4789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 644034299) ^ 322017149 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 644034299) ^ 33896542 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 644034299) ^ 181982 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 644034299) ^ 134482 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_662222287 : Nat.Prime 662222287 := by
  apply lucas_primality 662222287 (3 : ZMod 662222287)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (3344557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (3344557, 1)] : List FactorBlock).map factorBlockValue).prod) = 662222287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_3344557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 662222287) ^ 331111143 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 662222287) ^ 220740762 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 662222287) ^ 60202026 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 662222287) ^ 198 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_889731133 : Nat.Prime 889731133 := by
  apply lucas_primality 889731133 (2 : ZMod 889731133)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod) = 889731133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_74144261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 889731133) ^ 444865566 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 296577044 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 12 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_939845719 : Nat.Prime 939845719 := by
  apply lucas_primality 939845719 (13 : ZMod 939845719)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (7459093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (7459093, 1)] : List FactorBlock).map factorBlockValue).prod) = 939845719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_7459093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 939845719) ^ 469922859 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 939845719) ^ 313281906 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 939845719) ^ 134263674 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 939845719) ^ 126 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_963143029 : Nat.Prime 963143029 := by
  apply lucas_primality 963143029 (2 : ZMod 963143029)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod) = 963143029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_8917991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 963143029) ^ 481571514 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 321047676 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 108 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1025159417 : Nat.Prime 1025159417 := by
  apply lucas_primality 1025159417 (3 : ZMod 1025159417)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (128144927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (128144927, 1)] : List FactorBlock).map factorBlockValue).prod) = 1025159417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_128144927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1025159417) ^ 512579708 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1025159417) ^ 8 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1193048359 : Nat.Prime 1193048359 := by
  apply lucas_primality 1193048359 (3 : ZMod 1193048359)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (2800583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (2800583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193048359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_71
      · exact prime_fiftyFiveBA_2800583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1193048359) ^ 596524179 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193048359) ^ 397682786 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193048359) ^ 16803498 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193048359) ^ 426 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1300489019 : Nat.Prime 1300489019 := by
  apply lucas_primality 1300489019 (2 : ZMod 1300489019)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (2249981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (2249981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1300489019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_2249981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1300489019) ^ 650244509 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1300489019) ^ 76499354 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1300489019) ^ 578 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1381714183 : Nat.Prime 1381714183 := by
  apply lucas_primality 1381714183 (5 : ZMod 1381714183)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2753, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2753, 1), (27883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1381714183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_2753
      · exact prime_fiftyFiveBA_27883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1381714183) ^ 690857091 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1381714183) ^ 460571394 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1381714183) ^ 501894 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1381714183) ^ 49554 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1648045081 : Nat.Prime 1648045081 := by
  apply lucas_primality 1648045081 (31 : ZMod 1648045081)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (73, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (73, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1648045081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_73
      · exact prime_fiftyFiveBA_5701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1648045081) ^ 824022540 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1648045081) ^ 549348360 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1648045081) ^ 329609016 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1648045081) ^ 149822280 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1648045081) ^ 22575960 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1648045081) ^ 289080 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1858571623 : Nat.Prime 1858571623 := by
  apply lucas_primality 1858571623 (3 : ZMod 1858571623)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (34417993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (34417993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1858571623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_34417993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1858571623) ^ 929285811 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1858571623) ^ 619523874 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1858571623) ^ 54 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1979645233 : Nat.Prime 1979645233 := by
  apply lucas_primality 1979645233 (5 : ZMod 1979645233)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41242609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41242609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1979645233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_41242609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1979645233) ^ 989822616 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1979645233) ^ 659881744 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1979645233) ^ 48 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2064319931 : Nat.Prime 2064319931 := by
  apply lucas_primality 2064319931 (2 : ZMod 2064319931)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2064319931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_401
      · exact prime_fiftyFiveBA_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2064319931) ^ 1032159965 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 412863986 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 5147930 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 4010 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2276072291 : Nat.Prime 2276072291 := by
  apply lucas_primality 2276072291 (2 : ZMod 2276072291)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (4842707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (4842707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2276072291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_4842707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2276072291) ^ 1138036145 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2276072291) ^ 455214458 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2276072291) ^ 48427070 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2276072291) ^ 470 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2357567189 : Nat.Prime 2357567189 := by
  apply lucas_primality 2357567189 (2 : ZMod 2357567189)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (173, 2), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (173, 2), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2357567189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_173
      · exact prime_fiftyFiveBA_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2357567189) ^ 1178783594 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2357567189) ^ 50161004 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2357567189) ^ 13627556 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2357567189) ^ 5626652 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_61
      · exact prime_fiftyFiveBA_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2851043827 : Nat.Prime 2851043827 := by
  apply lucas_primality 2851043827 (2 : ZMod 2851043827)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17291, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17291, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2851043827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_17291
      · exact prime_fiftyFiveBA_27481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2851043827) ^ 1425521913 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851043827) ^ 950347942 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851043827) ^ 164886 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851043827) ^ 103746 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2871090773 : Nat.Prime 2871090773 := by
  apply lucas_primality 2871090773 (2 : ZMod 2871090773)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871090773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_1231171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871090773) ^ 1435545386 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 261008252 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 54171524 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 2332 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3339456559 : Nat.Prime 3339456559 := by
  apply lucas_primality 3339456559 (21 : ZMod 3339456559)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (941, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (941, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) = 3339456559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_79
      · exact prime_fiftyFiveBA_941
      · exact prime_fiftyFiveBA_7487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 3339456559) ^ 1669728279 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (21 : ZMod 3339456559) ^ 1113152186 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (21 : ZMod 3339456559) ^ 42271602 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (21 : ZMod 3339456559) ^ 3548838 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (21 : ZMod 3339456559) ^ 446034 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4146381443 : Nat.Prime 4146381443 := by
  apply lucas_primality 4146381443 (2 : ZMod 4146381443)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (12876961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (12876961, 1)] : List FactorBlock).map factorBlockValue).prod) = 4146381443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_12876961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4146381443) ^ 2073190721 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146381443) ^ 592340206 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146381443) ^ 180277454 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146381443) ^ 322 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4341064667 : Nat.Prime 4341064667 := by
  apply lucas_primality 4341064667 (2 : ZMod 4341064667)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (47, 1), (48973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (47, 1), (48973, 1)] : List FactorBlock).map factorBlockValue).prod) = 4341064667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_48973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4341064667) ^ 2170532333 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341064667) ^ 188741942 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341064667) ^ 105879626 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341064667) ^ 92363078 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341064667) ^ 88642 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4553531449 : Nat.Prime 4553531449 := by
  apply lucas_primality 4553531449 (14 : ZMod 4553531449)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (189730477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (189730477, 1)] : List FactorBlock).map factorBlockValue).prod) = 4553531449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_189730477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 4553531449) ^ 2276765724 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (14 : ZMod 4553531449) ^ 1517843816 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (14 : ZMod 4553531449) ^ 24 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4654512227 : Nat.Prime 4654512227 := by
  apply lucas_primality 4654512227 (2 : ZMod 4654512227)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (25574243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (25574243, 1)] : List FactorBlock).map factorBlockValue).prod) = 4654512227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_25574243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4654512227) ^ 2327256113 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4654512227) ^ 664930318 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4654512227) ^ 358039402 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4654512227) ^ 182 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5118840821 : Nat.Prime 5118840821 := by
  apply lucas_primality 5118840821 (2 : ZMod 5118840821)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118840821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_1291
      · exact prime_fiftyFiveBA_198251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5118840821) ^ 2559420410 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 1023768164 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 3965020 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 25820 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5405121677 : Nat.Prime 5405121677 := by
  apply lucas_primality 5405121677 (2 : ZMod 5405121677)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (32958059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (32958059, 1)] : List FactorBlock).map factorBlockValue).prod) = 5405121677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_32958059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5405121677) ^ 2702560838 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5405121677) ^ 131832236 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5405121677) ^ 164 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5789592673 : Nat.Prime 5789592673 := by
  apply lucas_primality 5789592673 (10 : ZMod 5789592673)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5789592673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_60308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5789592673) ^ 2894796336 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 1929864224 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 96 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_7088013991 : Nat.Prime 7088013991 := by
  apply lucas_primality 7088013991 (11 : ZMod 7088013991)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) = 7088013991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_151
      · exact prime_fiftyFiveBA_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7088013991) ^ 3544006995 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 2362671330 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 1417602798 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 172878390 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 46940490 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 557190 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8567186909 : Nat.Prime 8567186909 := by
  apply lucas_primality 8567186909 (2 : ZMod 8567186909)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (53, 1), (186227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (53, 1), (186227, 1)] : List FactorBlock).map factorBlockValue).prod) = 8567186909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_186227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8567186909) ^ 4283593454 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8567186909) ^ 1223883844 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8567186909) ^ 276360868 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8567186909) ^ 161645036 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8567186909) ^ 46004 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8850648943 : Nat.Prime 8850648943 := by
  apply lucas_primality 8850648943 (3 : ZMod 8850648943)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19157, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19157, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) = 8850648943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_19157
      · exact prime_fiftyFiveBA_25667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8850648943) ^ 4425324471 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8850648943) ^ 2950216314 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8850648943) ^ 462006 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8850648943) ^ 344826 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_9296318363 : Nat.Prime 9296318363 := by
  apply lucas_primality 9296318363 (2 : ZMod 9296318363)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (78782359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (78782359, 1)] : List FactorBlock).map factorBlockValue).prod) = 9296318363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_78782359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9296318363) ^ 4648159181 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 9296318363) ^ 157564718 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 9296318363) ^ 118 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_11339536811 : Nat.Prime 11339536811 := by
  apply lucas_primality 11339536811 (6 : ZMod 11339536811)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11339536811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_5225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11339536811) ^ 5669768405 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2267907362 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 1619933830 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 365791510 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2170 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_349
      · exact prime_fiftyFiveBA_619
      · exact prime_fiftyFiveBA_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_15113094193 : Nat.Prime 15113094193 := by
  apply lucas_primality 15113094193 (13 : ZMod 15113094193)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (317, 1), (47297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (317, 1), (47297, 1)] : List FactorBlock).map factorBlockValue).prod) = 15113094193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_317
      · exact prime_fiftyFiveBA_47297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 15113094193) ^ 7556547096 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 15113094193) ^ 5037698064 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 15113094193) ^ 2159013456 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 15113094193) ^ 47675376 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 15113094193) ^ 319536 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_15837208853 : Nat.Prime 15837208853 := by
  apply lucas_primality 15837208853 (2 : ZMod 15837208853)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) = 15837208853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_9257
      · exact prime_fiftyFiveBA_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15837208853) ^ 7918604426 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 833537308 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 1710836 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 703532 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_18299340599 : Nat.Prime 18299340599 := by
  apply lucas_primality 18299340599 (7 : ZMod 18299340599)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod) = 18299340599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_118826887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18299340599) ^ 9149670299 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 2614191514 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 1663576418 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 154 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_18827391551 : Nat.Prime 18827391551 := by
  apply lucas_primality 18827391551 (11 : ZMod 18827391551)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (34231621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (34231621, 1)] : List FactorBlock).map factorBlockValue).prod) = 18827391551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_34231621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 18827391551) ^ 9413695775 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 18827391551) ^ 3765478310 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 18827391551) ^ 1711581050 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 18827391551) ^ 550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_19046062171 : Nat.Prime 19046062171 := by
  apply lucas_primality 19046062171 (10 : ZMod 19046062171)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (139, 2), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (139, 2), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 19046062171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_139
      · exact prime_fiftyFiveBA_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19046062171) ^ 9523031085 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19046062171) ^ 6348687390 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19046062171) ^ 3809212434 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19046062171) ^ 137022030 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19046062171) ^ 15650010 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_19748623057 : Nat.Prime 19748623057 := by
  apply lucas_primality 19748623057 (10 : ZMod 19748623057)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod) = 19748623057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_157
      · exact prime_fiftyFiveBA_39113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19748623057) ^ 9874311528 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 6582874352 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 294755568 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 125787408 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 504912 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_20817142373 : Nat.Prime 20817142373 := by
  apply lucas_primality 20817142373 (2 : ZMod 20817142373)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (400329661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (400329661, 1)] : List FactorBlock).map factorBlockValue).prod) = 20817142373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_400329661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20817142373) ^ 10408571186 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20817142373) ^ 1601318644 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20817142373) ^ 52 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_20865607757 : Nat.Prime 20865607757 := by
  apply lucas_primality 20865607757 (2 : ZMod 20865607757)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (17330239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (17330239, 1)] : List FactorBlock).map factorBlockValue).prod) = 20865607757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_17330239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20865607757) ^ 10432803878 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20865607757) ^ 2980801108 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20865607757) ^ 485246692 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20865607757) ^ 1204 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_28972335619 : Nat.Prime 28972335619 := by
  apply lucas_primality 28972335619 (2 : ZMod 28972335619)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (69981487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (69981487, 1)] : List FactorBlock).map factorBlockValue).prod) = 28972335619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_69981487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28972335619) ^ 14486167809 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28972335619) ^ 9657445206 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28972335619) ^ 1259666766 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28972335619) ^ 414 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_29304298123 : Nat.Prime 29304298123 := by
  apply lucas_primality 29304298123 (2 : ZMod 29304298123)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod) = 29304298123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_1229
      · exact prime_fiftyFiveBA_32843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29304298123) ^ 14652149061 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 9768099374 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 2664027102 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 23844018 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 892254 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_36598681199 : Nat.Prime 36598681199 := by
  apply lucas_primality 36598681199 (11 : ZMod 36598681199)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod) = 36598681199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_18299340599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 36598681199) ^ 18299340599 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 36598681199) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_39324099029 : Nat.Prime 39324099029 := by
  apply lucas_primality 39324099029 (2 : ZMod 39324099029)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (427435859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (427435859, 1)] : List FactorBlock).map factorBlockValue).prod) = 39324099029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_427435859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39324099029) ^ 19662049514 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39324099029) ^ 1709743436 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39324099029) ^ 92 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_43052110799 : Nat.Prime 43052110799 := by
  apply lucas_primality 43052110799 (11 : ZMod 43052110799)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (7253, 1), (33347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (7253, 1), (33347, 1)] : List FactorBlock).map factorBlockValue).prod) = 43052110799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_7253
      · exact prime_fiftyFiveBA_33347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 43052110799) ^ 21526055399 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 43052110799) ^ 483731582 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 43052110799) ^ 5935766 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 43052110799) ^ 1291034 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_47842966141 : Nat.Prime 47842966141 := by
  apply lucas_primality 47842966141 (6 : ZMod 47842966141)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (829, 1), (961861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (829, 1), (961861, 1)] : List FactorBlock).map factorBlockValue).prod) = 47842966141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_829
      · exact prime_fiftyFiveBA_961861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 47842966141) ^ 23921483070 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 47842966141) ^ 15947655380 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 47842966141) ^ 9568593228 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 47842966141) ^ 57711660 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 47842966141) ^ 49740 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_51220428631 : Nat.Prime 51220428631 := by
  apply lucas_primality 51220428631 (3 : ZMod 51220428631)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (17, 1), (523, 1), (3919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (17, 1), (523, 1), (3919, 1)] : List FactorBlock).map factorBlockValue).prod) = 51220428631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_523
      · exact prime_fiftyFiveBA_3919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51220428631) ^ 25610214315 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 17073476210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 10244085726 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 7317204090 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 3012966390 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 97935810 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 51220428631) ^ 13069770 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_52767499787 : Nat.Prime 52767499787 := by
  apply lucas_primality 52767499787 (2 : ZMod 52767499787)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1109, 1), (23790577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1109, 1), (23790577, 1)] : List FactorBlock).map factorBlockValue).prod) = 52767499787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_1109
      · exact prime_fiftyFiveBA_23790577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52767499787) ^ 26383749893 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52767499787) ^ 47581154 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52767499787) ^ 2218 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_54819625657 : Nat.Prime 54819625657 := by
  apply lucas_primality 54819625657 (7 : ZMod 54819625657)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod) = 54819625657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_34091807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 54819625657) ^ 27409812828 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 18273208552 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 818203368 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 1608 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_57630359233 : Nat.Prime 57630359233 := by
  apply lucas_primality 57630359233 (5 : ZMod 57630359233)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (47, 1), (2128781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (47, 1), (2128781, 1)] : List FactorBlock).map factorBlockValue).prod) = 57630359233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_2128781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57630359233) ^ 28815179616 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 57630359233) ^ 19210119744 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 57630359233) ^ 1226177856 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 57630359233) ^ 27072 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_84756586553 : Nat.Prime 84756586553 := by
  apply lucas_primality 84756586553 (3 : ZMod 84756586553)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod) = 84756586553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_963143029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84756586553) ^ 42378293276 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 7705144232 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 88 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_86203997777 : Nat.Prime 86203997777 := by
  apply lucas_primality 86203997777 (3 : ZMod 86203997777)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (97, 1), (4272601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (97, 1), (4272601, 1)] : List FactorBlock).map factorBlockValue).prod) = 86203997777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_97
      · exact prime_fiftyFiveBA_4272601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86203997777) ^ 43101998888 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86203997777) ^ 6631076752 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86203997777) ^ 888701008 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86203997777) ^ 20176 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_95355923357 : Nat.Prime 95355923357 := by
  apply lucas_primality 95355923357 (2 : ZMod 95355923357)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (433, 1), (1021, 1), (53923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (433, 1), (1021, 1), (53923, 1)] : List FactorBlock).map factorBlockValue).prod) = 95355923357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_433
      · exact prime_fiftyFiveBA_1021
      · exact prime_fiftyFiveBA_53923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95355923357) ^ 47677961678 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95355923357) ^ 220221532 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95355923357) ^ 93394636 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95355923357) ^ 1768372 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_190507613573 : Nat.Prime 190507613573 := by
  apply lucas_primality 190507613573 (2 : ZMod 190507613573)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) = 190507613573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_727
      · exact prime_fiftyFiveBA_3691
      · exact prime_fiftyFiveBA_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190507613573) ^ 95253806786 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 262046236 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 51614092 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 10733428 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_260519272661 : Nat.Prime 260519272661 := by
  apply lucas_primality 260519272661 (3 : ZMod 260519272661)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) = 260519272661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_25439
      · exact prime_fiftyFiveBA_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260519272661) ^ 130259636330 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 52103854532 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 10240940 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 508780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_357219662081 : Nat.Prime 357219662081 := by
  apply lucas_primality 357219662081 (3 : ZMod 357219662081)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (279077861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (279077861, 1)] : List FactorBlock).map factorBlockValue).prod) = 357219662081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_279077861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 357219662081) ^ 178609831040 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 357219662081) ^ 71443932416 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 357219662081) ^ 1280 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_362865177953 : Nat.Prime 362865177953 := by
  apply lucas_primality 362865177953 (3 : ZMod 362865177953)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod) = 362865177953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_11339536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 362865177953) ^ 181432588976 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 362865177953) ^ 32 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_381657548039 : Nat.Prime 381657548039 := by
  apply lucas_primality 381657548039 (11 : ZMod 381657548039)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (219091589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (219091589, 1)] : List FactorBlock).map factorBlockValue).prod) = 381657548039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_219091589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 381657548039) ^ 190828774019 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 381657548039) ^ 29358272926 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 381657548039) ^ 5696381314 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 381657548039) ^ 1742 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_422139998297 : Nat.Prime 422139998297 := by
  apply lucas_primality 422139998297 (3 : ZMod 422139998297)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (52767499787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (52767499787, 1)] : List FactorBlock).map factorBlockValue).prod) = 422139998297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_52767499787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 422139998297) ^ 211069999148 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 422139998297) ^ 8 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_470838385529 : Nat.Prime 470838385529 := by
  apply lucas_primality 470838385529 (3 : ZMod 470838385529)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (43, 1), (5351, 1), (36541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (43, 1), (5351, 1), (36541, 1)] : List FactorBlock).map factorBlockValue).prod) = 470838385529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_5351
      · exact prime_fiftyFiveBA_36541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 470838385529) ^ 235419192764 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 470838385529) ^ 67262626504 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 470838385529) ^ 10949729896 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 470838385529) ^ 87990728 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 470838385529) ^ 12885208 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_602729551187 : Nat.Prime 602729551187 := by
  apply lucas_primality 602729551187 (2 : ZMod 602729551187)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43052110799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43052110799, 1)] : List FactorBlock).map factorBlockValue).prod) = 602729551187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_43052110799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 602729551187) ^ 301364775593 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 602729551187) ^ 86104221598 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 602729551187) ^ 14 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_689631982217 : Nat.Prime 689631982217 := by
  apply lucas_primality 689631982217 (3 : ZMod 689631982217)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (86203997777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (86203997777, 1)] : List FactorBlock).map factorBlockValue).prod) = 689631982217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_86203997777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 689631982217) ^ 344815991108 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 689631982217) ^ 8 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_714439324163 : Nat.Prime 714439324163 := by
  apply lucas_primality 714439324163 (2 : ZMod 714439324163)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (357219662081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (357219662081, 1)] : List FactorBlock).map factorBlockValue).prod) = 714439324163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_357219662081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 714439324163) ^ 357219662081 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 714439324163) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_743454511213 : Nat.Prime 743454511213 := by
  apply lucas_primality 743454511213 (2 : ZMod 743454511213)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (8850648943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (8850648943, 1)] : List FactorBlock).map factorBlockValue).prod) = 743454511213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_8850648943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 743454511213) ^ 371727255606 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 743454511213) ^ 247818170404 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 743454511213) ^ 106207787316 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 743454511213) ^ 84 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_835144542671 : Nat.Prime 835144542671 := by
  apply lucas_primality 835144542671 (23 : ZMod 835144542671)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (23, 1), (1319, 1), (144889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (23, 1), (1319, 1), (144889, 1)] : List FactorBlock).map factorBlockValue).prod) = 835144542671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_1319
      · exact prime_fiftyFiveBA_144889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 835144542671) ^ 417572271335 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 835144542671) ^ 167028908534 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 835144542671) ^ 43954975930 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 835144542671) ^ 36310632290 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 835144542671) ^ 633164930 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (23 : ZMod 835144542671) ^ 5764030 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_911836775173 : Nat.Prime 911836775173 := by
  apply lucas_primality 911836775173 (5 : ZMod 911836775173)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (196429, 1), (386839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (196429, 1), (386839, 1)] : List FactorBlock).map factorBlockValue).prod) = 911836775173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_196429
      · exact prime_fiftyFiveBA_386839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 911836775173) ^ 455918387586 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 911836775173) ^ 303945591724 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 911836775173) ^ 4642068 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 911836775173) ^ 2357148 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_941676771059 : Nat.Prime 941676771059 := by
  apply lucas_primality 941676771059 (2 : ZMod 941676771059)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (470838385529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (470838385529, 1)] : List FactorBlock).map factorBlockValue).prod) = 941676771059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_470838385529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 941676771059) ^ 470838385529 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 941676771059) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1143045681439 : Nat.Prime 1143045681439 := by
  apply lucas_primality 1143045681439 (6 : ZMod 1143045681439)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143045681439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_190507613573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1143045681439) ^ 571522840719 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 381015227146 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_397
      · exact prime_fiftyFiveBA_977
      · exact prime_fiftyFiveBA_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_35279
      · exact prime_fiftyFiveBA_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1530118336289 : Nat.Prime 1530118336289 := by
  apply lucas_primality 1530118336289 (3 : ZMod 1530118336289)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4457, 1), (10728337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4457, 1), (10728337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530118336289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_4457
      · exact prime_fiftyFiveBA_10728337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1530118336289) ^ 765059168144 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1530118336289) ^ 343306784 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1530118336289) ^ 142624 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1545589339391 : Nat.Prime 1545589339391 := by
  apply lucas_primality 1545589339391 (17 : ZMod 1545589339391)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (1667, 1), (850613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (1667, 1), (850613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1545589339391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_109
      · exact prime_fiftyFiveBA_1667
      · exact prime_fiftyFiveBA_850613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1545589339391) ^ 772794669695 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1545589339391) ^ 309117867878 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1545589339391) ^ 14179718710 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1545589339391) ^ 927168170 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1545589339391) ^ 1817030 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2155474125481 : Nat.Prime 2155474125481 := by
  apply lucas_primality 2155474125481 (7 : ZMod 2155474125481)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (1381714183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (1381714183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2155474125481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_1381714183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2155474125481) ^ 1077737062740 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2155474125481) ^ 718491375160 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2155474125481) ^ 431094825096 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2155474125481) ^ 165805701960 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2155474125481) ^ 1560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2630685188203 : Nat.Prime 2630685188203 := by
  apply lucas_primality 2630685188203 (2 : ZMod 2630685188203)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (4341064667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (4341064667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2630685188203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_101
      · exact prime_fiftyFiveBA_4341064667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2630685188203) ^ 1315342594101 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630685188203) ^ 876895062734 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630685188203) ^ 26046388002 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2630685188203) ^ 606 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2830921604983 : Nat.Prime 2830921604983 := by
  apply lucas_primality 2830921604983 (6 : ZMod 2830921604983)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (971, 1), (1603669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (971, 1), (1603669, 1)] : List FactorBlock).map factorBlockValue).prod) = 2830921604983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_101
      · exact prime_fiftyFiveBA_971
      · exact prime_fiftyFiveBA_1603669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2830921604983) ^ 1415460802491 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2830921604983) ^ 943640534994 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2830921604983) ^ 28028926782 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2830921604983) ^ 2915470242 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2830921604983) ^ 1765278 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2909674311721 : Nat.Prime 2909674311721 := by
  apply lucas_primality 2909674311721 (13 : ZMod 2909674311721)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2909674311721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_191
      · exact prime_fiftyFiveBA_11540831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2909674311721) ^ 1454837155860 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 969891437240 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 581934862344 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 264515846520 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 15233896920 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 252120 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_761
      · exact prime_fiftyFiveBA_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3112039398583 : Nat.Prime 3112039398583 := by
  apply lucas_primality 3112039398583 (3 : ZMod 3112039398583)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (57630359233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (57630359233, 1)] : List FactorBlock).map factorBlockValue).prod) = 3112039398583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_57630359233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3112039398583) ^ 1556019699291 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3112039398583) ^ 1037346466194 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3112039398583) ^ 54 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3496992739049 : Nat.Prime 3496992739049 := by
  apply lucas_primality 3496992739049 (3 : ZMod 3496992739049)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3496992739049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_103
      · exact prime_fiftyFiveBA_98695889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3496992739049) ^ 1748496369524 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 81325412536 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 33951385816 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 35432 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4819414370321 : Nat.Prime 4819414370321 := by
  apply lucas_primality 4819414370321 (3 : ZMod 4819414370321)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod) = 4819414370321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_2081
      · exact prime_fiftyFiveBA_154807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4819414370321) ^ 2409707185160 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 963882874064 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 438128579120 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 283494962960 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 2315912720 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 31131760 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4893884368619 : Nat.Prime 4893884368619 := by
  apply lucas_primality 4893884368619 (2 : ZMod 4893884368619)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (293, 1), (1193048359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (293, 1), (1193048359, 1)] : List FactorBlock).map factorBlockValue).prod) = 4893884368619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_293
      · exact prime_fiftyFiveBA_1193048359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4893884368619) ^ 2446942184309 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4893884368619) ^ 699126338374 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4893884368619) ^ 16702677026 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4893884368619) ^ 4102 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5093525001451 : Nat.Prime 5093525001451 := by
  apply lucas_primality 5093525001451 (10 : ZMod 5093525001451)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (59387, 1), (571789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (59387, 1), (571789, 1)] : List FactorBlock).map factorBlockValue).prod) = 5093525001451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_59387
      · exact prime_fiftyFiveBA_571789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5093525001451) ^ 2546762500725 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5093525001451) ^ 1697841667150 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5093525001451) ^ 1018705000290 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5093525001451) ^ 85768350 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5093525001451) ^ 8908050 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_381559
      · exact prime_fiftyFiveBA_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5262266536651 : Nat.Prime 5262266536651 := by
  apply lucas_primality 5262266536651 (2 : ZMod 5262266536651)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (43, 1), (293, 1), (928163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (43, 1), (293, 1), (928163, 1)] : List FactorBlock).map factorBlockValue).prod) = 5262266536651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_293
      · exact prime_fiftyFiveBA_928163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5262266536651) ^ 2631133268325 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5262266536651) ^ 1754088845550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5262266536651) ^ 1052453307330 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5262266536651) ^ 122378291550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5262266536651) ^ 17959954050 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5262266536651) ^ 5669550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_7119462691567 : Nat.Prime 7119462691567 := by
  apply lucas_primality 7119462691567 (3 : ZMod 7119462691567)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (20817142373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (20817142373, 1)] : List FactorBlock).map factorBlockValue).prod) = 7119462691567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_20817142373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7119462691567) ^ 3559731345783 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7119462691567) ^ 2373154230522 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7119462691567) ^ 374708562714 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7119462691567) ^ 342 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_7423009264091 : Nat.Prime 7423009264091 := by
  apply lucas_primality 7423009264091 (2 : ZMod 7423009264091)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (19, 1), (167, 1), (1231, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (19, 1), (167, 1), (1231, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 7423009264091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_167
      · exact prime_fiftyFiveBA_1231
      · exact prime_fiftyFiveBA_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7423009264091) ^ 3711504632045 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 1484601852818 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 1060429894870 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 436647603770 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 390684698110 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 44449157270 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 6030064390 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423009264091) ^ 4648095970 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8305487066761 : Nat.Prime 8305487066761 := by
  apply lucas_primality 8305487066761 (7 : ZMod 8305487066761)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (54521, 1), (97651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (54521, 1), (97651, 1)] : List FactorBlock).map factorBlockValue).prod) = 8305487066761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_54521
      · exact prime_fiftyFiveBA_97651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8305487066761) ^ 4152743533380 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8305487066761) ^ 2768495688920 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8305487066761) ^ 1661097413352 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8305487066761) ^ 638883620520 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8305487066761) ^ 152335560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8305487066761) ^ 85052760 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8595391086979 : Nat.Prime 8595391086979 := by
  apply lucas_primality 8595391086979 (2 : ZMod 8595391086979)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5741, 1), (249532343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5741, 1), (249532343, 1)] : List FactorBlock).map factorBlockValue).prod) = 8595391086979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5741
      · exact prime_fiftyFiveBA_249532343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8595391086979) ^ 4297695543489 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595391086979) ^ 2865130362326 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595391086979) ^ 1497194058 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595391086979) ^ 34446 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8685491862457 : Nat.Prime 8685491862457 := by
  apply lucas_primality 8685491862457 (10 : ZMod 8685491862457)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (53, 1), (2276072291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (53, 1), (2276072291, 1)] : List FactorBlock).map factorBlockValue).prod) = 8685491862457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_2276072291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8685491862457) ^ 4342745931228 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 8685491862457) ^ 2895163954152 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 8685491862457) ^ 163877204952 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 8685491862457) ^ 3816 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8921454134557 : Nat.Prime 8921454134557 := by
  apply lucas_primality 8921454134557 (5 : ZMod 8921454134557)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (743454511213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (743454511213, 1)] : List FactorBlock).map factorBlockValue).prod) = 8921454134557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_743454511213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8921454134557) ^ 4460727067278 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 8921454134557) ^ 2973818044852 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 8921454134557) ^ 12 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_9099828029177 : Nat.Prime 9099828029177 := by
  apply lucas_primality 9099828029177 (3 : ZMod 9099828029177)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (15073, 1), (705277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (15073, 1), (705277, 1)] : List FactorBlock).map factorBlockValue).prod) = 9099828029177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_107
      · exact prime_fiftyFiveBA_15073
      · exact prime_fiftyFiveBA_705277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9099828029177) ^ 4549914014588 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9099828029177) ^ 85045121768 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9099828029177) ^ 603717112 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9099828029177) ^ 12902488 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_13833328385243 : Nat.Prime 13833328385243 := by
  apply lucas_primality 13833328385243 (2 : ZMod 13833328385243)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (201473, 1), (434563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (201473, 1), (434563, 1)] : List FactorBlock).map factorBlockValue).prod) = 13833328385243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_79
      · exact prime_fiftyFiveBA_201473
      · exact prime_fiftyFiveBA_434563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13833328385243) ^ 6916664192621 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13833328385243) ^ 175105422598 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13833328385243) ^ 68660954 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13833328385243) ^ 31832734 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_14235312515719 : Nat.Prime 14235312515719 := by
  apply lucas_primality 14235312515719 (6 : ZMod 14235312515719)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (83, 1), (240209789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (83, 1), (240209789, 1)] : List FactorBlock).map factorBlockValue).prod) = 14235312515719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_83
      · exact prime_fiftyFiveBA_240209789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14235312515719) ^ 7117656257859 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14235312515719) ^ 4745104171906 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14235312515719) ^ 2033616073674 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14235312515719) ^ 837371324454 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14235312515719) ^ 171509789346 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14235312515719) ^ 59262 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_14624949386309 : Nat.Prime 14624949386309 := by
  apply lucas_primality 14624949386309 (2 : ZMod 14624949386309)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (28663, 1), (2091139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (28663, 1), (2091139, 1)] : List FactorBlock).map factorBlockValue).prod) = 14624949386309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_61
      · exact prime_fiftyFiveBA_28663
      · exact prime_fiftyFiveBA_2091139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14624949386309) ^ 7312474693154 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14624949386309) ^ 239753268628 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14624949386309) ^ 510237916 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14624949386309) ^ 6993772 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_16551167573209 : Nat.Prime 16551167573209 := by
  apply lucas_primality 16551167573209 (7 : ZMod 16551167573209)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (689631982217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (689631982217, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551167573209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_689631982217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 16551167573209) ^ 8275583786604 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16551167573209) ^ 5517055857736 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16551167573209) ^ 24 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_20927806250941 : Nat.Prime 20927806250941 := by
  apply lucas_primality 20927806250941 (11 : ZMod 20927806250941)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (89, 1), (7823, 1), (55663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (89, 1), (7823, 1), (55663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20927806250941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_7823
      · exact prime_fiftyFiveBA_55663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20927806250941) ^ 10463903125470 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 20927806250941) ^ 6975935416980 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 20927806250941) ^ 4185561250188 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 20927806250941) ^ 235143890460 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 20927806250941) ^ 2675163780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 20927806250941) ^ 375973380 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_21106999914851 : Nat.Prime 21106999914851 := by
  apply lucas_primality 21106999914851 (2 : ZMod 21106999914851)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (422139998297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (422139998297, 1)] : List FactorBlock).map factorBlockValue).prod) = 21106999914851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_422139998297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21106999914851) ^ 10553499957425 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21106999914851) ^ 4221399982970 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21106999914851) ^ 50 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_23505080912179 : Nat.Prime 23505080912179 := by
  apply lucas_primality 23505080912179 (2 : ZMod 23505080912179)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22483, 1), (174243361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22483, 1), (174243361, 1)] : List FactorBlock).map factorBlockValue).prod) = 23505080912179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_22483
      · exact prime_fiftyFiveBA_174243361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23505080912179) ^ 11752540456089 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23505080912179) ^ 7835026970726 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23505080912179) ^ 1045460166 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23505080912179) ^ 134898 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_23882827256521 : Nat.Prime 23882827256521 := by
  apply lucas_primality 23882827256521 (11 : ZMod 23882827256521)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 2), (227, 1), (3033757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 2), (227, 1), (3033757, 1)] : List FactorBlock).map factorBlockValue).prod) = 23882827256521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_227
      · exact prime_fiftyFiveBA_3033757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23882827256521) ^ 11941413628260 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 23882827256521) ^ 7960942418840 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 23882827256521) ^ 4776565451304 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 23882827256521) ^ 1404872191560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 23882827256521) ^ 105210692760 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 23882827256521) ^ 7872360 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_28022106501281 : Nat.Prime 28022106501281 := by
  apply lucas_primality 28022106501281 (3 : ZMod 28022106501281)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (461, 1), (16447, 1), (23099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (461, 1), (16447, 1), (23099, 1)] : List FactorBlock).map factorBlockValue).prod) = 28022106501281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_461
      · exact prime_fiftyFiveBA_16447
      · exact prime_fiftyFiveBA_23099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28022106501281) ^ 14011053250640 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28022106501281) ^ 5604421300256 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28022106501281) ^ 60785480480 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28022106501281) ^ 1703782240 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28022106501281) ^ 1213130720 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_29567715968627 : Nat.Prime 29567715968627 := by
  apply lucas_primality 29567715968627 (2 : ZMod 29567715968627)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (5443, 1), (5253623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (5443, 1), (5253623, 1)] : List FactorBlock).map factorBlockValue).prod) = 29567715968627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_5443
      · exact prime_fiftyFiveBA_5253623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29567715968627) ^ 14783857984313 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29567715968627) ^ 2687974178966 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29567715968627) ^ 629100339758 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29567715968627) ^ 5432246182 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 29567715968627) ^ 5628062 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_30532603843121 : Nat.Prime 30532603843121 := by
  apply lucas_primality 30532603843121 (3 : ZMod 30532603843121)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (381657548039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (381657548039, 1)] : List FactorBlock).map factorBlockValue).prod) = 30532603843121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_381657548039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30532603843121) ^ 15266301921560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30532603843121) ^ 6106520768624 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30532603843121) ^ 80 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_36625047980509 : Nat.Prime 36625047980509 := by
  apply lucas_primality 36625047980509 (2 : ZMod 36625047980509)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (293, 1), (267094367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (293, 1), (267094367, 1)] : List FactorBlock).map factorBlockValue).prod) = 36625047980509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_293
      · exact prime_fiftyFiveBA_267094367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36625047980509) ^ 18312523990254 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36625047980509) ^ 12208349326836 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36625047980509) ^ 2817311383116 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36625047980509) ^ 125000163756 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36625047980509) ^ 137124 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_45105424703291 : Nat.Prime 45105424703291 := by
  apply lucas_primality 45105424703291 (2 : ZMod 45105424703291)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (109, 1), (467, 1), (12658649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (109, 1), (467, 1), (12658649, 1)] : List FactorBlock).map factorBlockValue).prod) = 45105424703291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_109
      · exact prime_fiftyFiveBA_467
      · exact prime_fiftyFiveBA_12658649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45105424703291) ^ 22552712351645 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45105424703291) ^ 9021084940658 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45105424703291) ^ 6443632100470 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45105424703291) ^ 413811235810 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45105424703291) ^ 96585491870 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45105424703291) ^ 3563210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_56020723162777 : Nat.Prime 56020723162777 := by
  apply lucas_primality 56020723162777 (5 : ZMod 56020723162777)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod) = 56020723162777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_271
      · exact prime_fiftyFiveBA_2871090773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 56020723162777) ^ 28010361581388 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 18673574387592 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 206718535656 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 19512 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_59515030159927 : Nat.Prime 59515030159927 := by
  apply lucas_primality 59515030159927 (3 : ZMod 59515030159927)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (97, 1), (9296318363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (97, 1), (9296318363, 1)] : List FactorBlock).map factorBlockValue).prod) = 59515030159927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_97
      · exact prime_fiftyFiveBA_9296318363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59515030159927) ^ 29757515079963 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 59515030159927) ^ 19838343386642 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 59515030159927) ^ 5410457287266 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 59515030159927) ^ 613557011958 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 59515030159927) ^ 6402 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_94094173862137 : Nat.Prime 94094173862137 := by
  apply lucas_primality 94094173862137 (5 : ZMod 94094173862137)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (41, 1), (4553531449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (41, 1), (4553531449, 1)] : List FactorBlock).map factorBlockValue).prod) = 94094173862137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_4553531449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 94094173862137) ^ 47047086931068 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 94094173862137) ^ 31364724620712 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 94094173862137) ^ 13442024837448 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 94094173862137) ^ 2294979850296 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 94094173862137) ^ 20664 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_99304400168929 : Nat.Prime 99304400168929 := by
  apply lucas_primality 99304400168929 (11 : ZMod 99304400168929)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (19, 1), (59, 1), (307588711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (19, 1), (59, 1), (307588711, 1)] : List FactorBlock).map factorBlockValue).prod) = 99304400168929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_307588711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 99304400168929) ^ 49652200084464 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99304400168929) ^ 33101466722976 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99304400168929) ^ 5226547377312 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99304400168929) ^ 1683125426592 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99304400168929) ^ 322848 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_105576899039377 : Nat.Prime 105576899039377 := by
  apply lucas_primality 105576899039377 (5 : ZMod 105576899039377)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (607, 1), (54083423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (607, 1), (54083423, 1)] : List FactorBlock).map factorBlockValue).prod) = 105576899039377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_607
      · exact prime_fiftyFiveBA_54083423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 105576899039377) ^ 52788449519688 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105576899039377) ^ 35192299679792 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105576899039377) ^ 1575774612528 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105576899039377) ^ 173932288368 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105576899039377) ^ 1952112 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_110784210377741 : Nat.Prime 110784210377741 := by
  apply lucas_primality 110784210377741 (7 : ZMod 110784210377741)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod) = 110784210377741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_19841
      · exact prime_fiftyFiveBA_279180007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 110784210377741) ^ 55392105188870 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 22156842075548 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 5583600140 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 396820 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_126089608766851 : Nat.Prime 126089608766851 := by
  apply lucas_primality 126089608766851 (3 : ZMod 126089608766851)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (43, 1), (7187, 1), (906673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (43, 1), (7187, 1), (906673, 1)] : List FactorBlock).map factorBlockValue).prod) = 126089608766851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_7187
      · exact prime_fiftyFiveBA_906673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126089608766851) ^ 63044804383425 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 126089608766851) ^ 42029869588950 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 126089608766851) ^ 25217921753370 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 126089608766851) ^ 2932316482950 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 126089608766851) ^ 17544122550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 126089608766851) ^ 139068450 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_142486514597129 : Nat.Prime 142486514597129 := by
  apply lucas_primality 142486514597129 (3 : ZMod 142486514597129)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (17, 1), (6397, 1), (12598393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (17, 1), (6397, 1), (12598393, 1)] : List FactorBlock).map factorBlockValue).prod) = 142486514597129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_6397
      · exact prime_fiftyFiveBA_12598393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 142486514597129) ^ 71243257298564 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 142486514597129) ^ 10960501122856 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 142486514597129) ^ 8381559682184 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 142486514597129) ^ 22273958824 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 142486514597129) ^ 11309896 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_269887204737977 : Nat.Prime 269887204737977 := by
  apply lucas_primality 269887204737977 (3 : ZMod 269887204737977)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod) = 269887204737977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_4819414370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269887204737977) ^ 134943602368988 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 38555314962568 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 56 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_356546750101571 : Nat.Prime 356546750101571 := by
  apply lucas_primality 356546750101571 (6 : ZMod 356546750101571)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (5093525001451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (5093525001451, 1)] : List FactorBlock).map factorBlockValue).prod) = 356546750101571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_5093525001451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 356546750101571) ^ 178273375050785 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 356546750101571) ^ 71309350020314 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 356546750101571) ^ 50935250014510 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 356546750101571) ^ 70 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_422307596157509 : Nat.Prime 422307596157509 := by
  apply lucas_primality 422307596157509 (2 : ZMod 422307596157509)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (105576899039377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (105576899039377, 1)] : List FactorBlock).map factorBlockValue).prod) = 422307596157509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_105576899039377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 422307596157509) ^ 211153798078754 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 422307596157509) ^ 4 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_455535874848193 : Nat.Prime 455535874848193 := by
  apply lucas_primality 455535874848193 (10 : ZMod 455535874848193)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (108991, 1), (21768611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (108991, 1), (21768611, 1)] : List FactorBlock).map factorBlockValue).prod) = 455535874848193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_108991
      · exact prime_fiftyFiveBA_21768611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 455535874848193) ^ 227767937424096 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 455535874848193) ^ 151845291616064 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 455535874848193) ^ 4179573312 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 455535874848193) ^ 20926272 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1012564812501629 : Nat.Prime 1012564812501629 := by
  apply lucas_primality 1012564812501629 (2 : ZMod 1012564812501629)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012564812501629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_1883407
      · exact prime_fiftyFiveBA_134406001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1012564812501629) ^ 506282406250814 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 537624004 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 7533628 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1132865085569267 : Nat.Prime 1132865085569267 := by
  apply lucas_primality 1132865085569267 (2 : ZMod 1132865085569267)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1132865085569267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_223
      · exact prime_fiftyFiveBA_362865177953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1132865085569267) ^ 566432542784633 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 161837869367038 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 5080112491342 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 3122 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1139892116777033 : Nat.Prime 1139892116777033 := by
  apply lucas_primality 1139892116777033 (3 : ZMod 1139892116777033)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (142486514597129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (142486514597129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139892116777033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_142486514597129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1139892116777033) ^ 569946058388516 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139892116777033) ^ 8 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1634166383156653 : Nat.Prime 1634166383156653 := by
  apply lucas_primality 1634166383156653 (2 : ZMod 1634166383156653)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (1530118336289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (1530118336289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1634166383156653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_1530118336289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1634166383156653) ^ 817083191578326 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1634166383156653) ^ 544722127718884 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1634166383156653) ^ 18361420035468 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1634166383156653) ^ 1068 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3919860787867319 : Nat.Prime 3919860787867319 := by
  apply lucas_primality 3919860787867319 (7 : ZMod 3919860787867319)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83843, 1), (3339456559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83843, 1), (3339456559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3919860787867319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_83843
      · exact prime_fiftyFiveBA_3339456559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3919860787867319) ^ 1959930393933659 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3919860787867319) ^ 559980112552474 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3919860787867319) ^ 46752391826 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3919860787867319) ^ 1173802 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5671664637949631 : Nat.Prime 5671664637949631 := by
  apply lucas_primality 5671664637949631 (31 : ZMod 5671664637949631)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (13833328385243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (13833328385243, 1)] : List FactorBlock).map factorBlockValue).prod) = 5671664637949631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_13833328385243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 5671664637949631) ^ 2835832318974815 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 5671664637949631) ^ 1134332927589926 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 5671664637949631) ^ 138333283852430 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 5671664637949631) ^ 410 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5737922695986289 : Nat.Prime 5737922695986289 := by
  apply lucas_primality 5737922695986289 (17 : ZMod 5737922695986289)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 2), (157, 1), (293, 1), (3089941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 2), (157, 1), (293, 1), (3089941, 1)] : List FactorBlock).map factorBlockValue).prod) = 5737922695986289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_157
      · exact prime_fiftyFiveBA_293
      · exact prime_fiftyFiveBA_3089941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5737922695986289) ^ 2868961347993144 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 5737922695986289) ^ 1912640898662096 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 5737922695986289) ^ 197859403309872 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 5737922695986289) ^ 36547278318384 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 5737922695986289) ^ 19583353911216 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (17 : ZMod 5737922695986289) ^ 1856968368 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5915015824042901 : Nat.Prime 5915015824042901 := by
  apply lucas_primality 5915015824042901 (3 : ZMod 5915015824042901)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (37, 1), (163, 1), (316376989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (37, 1), (163, 1), (316376989, 1)] : List FactorBlock).map factorBlockValue).prod) = 5915015824042901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_163
      · exact prime_fiftyFiveBA_316376989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5915015824042901) ^ 2957507912021450 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915015824042901) ^ 1183003164808580 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915015824042901) ^ 190806962065900 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915015824042901) ^ 159865292541700 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915015824042901) ^ 36288440638300 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915015824042901) ^ 18696100 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8973711654617341 : Nat.Prime 8973711654617341 := by
  apply lucas_primality 8973711654617341 (2 : ZMod 8973711654617341)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (347, 1), (277247, 1), (518207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (347, 1), (277247, 1), (518207, 1)] : List FactorBlock).map factorBlockValue).prod) = 8973711654617341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_347
      · exact prime_fiftyFiveBA_277247
      · exact prime_fiftyFiveBA_518207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8973711654617341) ^ 4486855827308670 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8973711654617341) ^ 2991237218205780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8973711654617341) ^ 1794742330923468 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8973711654617341) ^ 25860840503220 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8973711654617341) ^ 32367209220 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8973711654617341) ^ 17316847620 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_10279120799235109 : Nat.Prime 10279120799235109 := by
  apply lucas_primality 10279120799235109 (6 : ZMod 10279120799235109)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod) = 10279120799235109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_347
      · exact prime_fiftyFiveBA_827
      · exact prime_fiftyFiveBA_28687
      · exact prime_fiftyFiveBA_104053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10279120799235109) ^ 5139560399617554 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 3426373599745036 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 29622826510764 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 12429408463404 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 358319824284 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 98787356436 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_16705093306204151 : Nat.Prime 16705093306204151 := by
  apply lucas_primality 16705093306204151 (7 : ZMod 16705093306204151)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (5113, 1), (11243, 1), (5811937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (5113, 1), (11243, 1), (5811937, 1)] : List FactorBlock).map factorBlockValue).prod) = 16705093306204151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_5113
      · exact prime_fiftyFiveBA_11243
      · exact prime_fiftyFiveBA_5811937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16705093306204151) ^ 8352546653102075 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16705093306204151) ^ 3341018661240830 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16705093306204151) ^ 3267180384550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16705093306204151) ^ 1485821694050 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16705093306204151) ^ 2874272950 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_23964608726411069 : Nat.Prime 23964608726411069 := by
  apply lucas_primality 23964608726411069 (2 : ZMod 23964608726411069)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9047041, 1), (662222287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9047041, 1), (662222287, 1)] : List FactorBlock).map factorBlockValue).prod) = 23964608726411069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_9047041
      · exact prime_fiftyFiveBA_662222287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23964608726411069) ^ 11982304363205534 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23964608726411069) ^ 2648889148 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23964608726411069) ^ 36188164 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_656951
      · exact prime_fiftyFiveBA_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_30492110377557209 : Nat.Prime 30492110377557209 := by
  apply lucas_primality 30492110377557209 (3 : ZMod 30492110377557209)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod) = 30492110377557209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_1637
      · exact prime_fiftyFiveBA_6529
      · exact prime_fiftyFiveBA_11503777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30492110377557209) ^ 15246055188778604 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 983616463792168 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 18626823688184 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 4670257371352 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 2650617304 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_55469069128015321 : Nat.Prime 55469069128015321 := by
  apply lucas_primality 55469069128015321 (31 : ZMod 55469069128015321)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (647, 1), (714439324163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (647, 1), (714439324163, 1)] : List FactorBlock).map factorBlockValue).prod) = 55469069128015321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_647
      · exact prime_fiftyFiveBA_714439324163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 55469069128015321) ^ 27734534564007660 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 55469069128015321) ^ 18489689709338440 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 55469069128015321) ^ 11093813825603064 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 55469069128015321) ^ 85732718899560 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (31 : ZMod 55469069128015321) ^ 77640 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_87803407596954793 : Nat.Prime 87803407596954793 := by
  apply lucas_primality 87803407596954793 (5 : ZMod 87803407596954793)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (257, 1), (14235312515719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (257, 1), (14235312515719, 1)] : List FactorBlock).map factorBlockValue).prod) = 87803407596954793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_257
      · exact prime_fiftyFiveBA_14235312515719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 87803407596954793) ^ 43901703798477396 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 87803407596954793) ^ 29267802532318264 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 87803407596954793) ^ 341647500377256 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 87803407596954793) ^ 6168 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_89292073564459247 : Nat.Prime 89292073564459247 := by
  apply lucas_primality 89292073564459247 (5 : ZMod 89292073564459247)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89292073564459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_110784210377741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 89292073564459247) ^ 44646036782229623 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 6868621043419942 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 2880389469821266 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 806 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_107302047888098879 : Nat.Prime 107302047888098879 := by
  apply lucas_primality 107302047888098879 (7 : ZMod 107302047888098879)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2816909, 1), (19046062171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2816909, 1), (19046062171, 1)] : List FactorBlock).map factorBlockValue).prod) = 107302047888098879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_2816909
      · exact prime_fiftyFiveBA_19046062171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 107302047888098879) ^ 53651023944049439 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 107302047888098879) ^ 38092124342 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 107302047888098879) ^ 5633818 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_115413075534405269 : Nat.Prime 115413075534405269 := by
  apply lucas_primality 115413075534405269 (2 : ZMod 115413075534405269)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1367, 1), (21106999914851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1367, 1), (21106999914851, 1)] : List FactorBlock).map factorBlockValue).prod) = 115413075534405269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_1367
      · exact prime_fiftyFiveBA_21106999914851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115413075534405269) ^ 57706537767202634 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 115413075534405269) ^ 84427999659404 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 115413075534405269) ^ 5468 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_330398329765458121 : Nat.Prime 330398329765458121 := by
  apply lucas_primality 330398329765458121 (7 : ZMod 330398329765458121)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (4129, 1), (73751, 1), (531857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (4129, 1), (73751, 1), (531857, 1)] : List FactorBlock).map factorBlockValue).prod) = 330398329765458121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_4129
      · exact prime_fiftyFiveBA_73751
      · exact prime_fiftyFiveBA_531857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 330398329765458121) ^ 165199164882729060 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 110132776588486040 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 66079665953091624 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 19435195868556360 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 80018970638280 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 4479916608120 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 330398329765458121) ^ 621216473160 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_374376818878815937 : Nat.Prime 374376818878815937 := by
  apply lucas_primality 374376818878815937 (5 : ZMod 374376818878815937)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod) = 374376818878815937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_35569
      · exact prime_fiftyFiveBA_54819625657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 374376818878815937) ^ 187188409439407968 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 124792272959605312 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 10525368126144 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 6829248 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_394542161159196257 : Nat.Prime 394542161159196257 := by
  apply lucas_primality 394542161159196257 (3 : ZMod 394542161159196257)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (73, 1), (2104699, 1), (80247329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (73, 1), (2104699, 1), (80247329, 1)] : List FactorBlock).map factorBlockValue).prod) = 394542161159196257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_73
      · exact prime_fiftyFiveBA_2104699
      · exact prime_fiftyFiveBA_80247329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 394542161159196257) ^ 197271080579598128 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394542161159196257) ^ 5404687139167072 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394542161159196257) ^ 187457760544 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394542161159196257) ^ 4916576864 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_554011756364663489 : Nat.Prime 554011756364663489 := by
  apply lucas_primality 554011756364663489 (3 : ZMod 554011756364663489)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod) = 554011756364663489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_10691
      · exact prime_fiftyFiveBA_19748623057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554011756364663489) ^ 277005878182331744 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 13512481862552768 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 51820386901568 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 28053184 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_61717
      · exact prime_fiftyFiveBA_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_826636823185963187 : Nat.Prime 826636823185963187 := by
  apply lucas_primality 826636823185963187 (2 : ZMod 826636823185963187)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod) = 826636823185963187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_80744533
      · exact prime_fiftyFiveBA_5118840821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 826636823185963187) ^ 413318411592981593 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 10237681642 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 161489066 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_859806059102301397 : Nat.Prime 859806059102301397 := by
  apply lucas_primality 859806059102301397 (2 : ZMod 859806059102301397)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod) = 859806059102301397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_1279
      · exact prime_fiftyFiveBA_56020723162777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 859806059102301397) ^ 429903029551150698 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 286602019700767132 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 672248677953324 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 15348 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_974357259695558663 : Nat.Prime 974357259695558663 := by
  apply lucas_primality 974357259695558663 (5 : ZMod 974357259695558663)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod) = 974357259695558663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_18217
      · exact prime_fiftyFiveBA_7088013991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 974357259695558663) ^ 487178629847779331 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 139193894242222666 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 88577932699596242 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 53486153576086 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 137465482 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1360064623232344999 : Nat.Prime 1360064623232344999 := by
  apply lucas_primality 1360064623232344999 (3 : ZMod 1360064623232344999)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (11801, 1), (835144542671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (11801, 1), (835144542671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1360064623232344999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_11801
      · exact prime_fiftyFiveBA_835144542671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1360064623232344999) ^ 680032311616172499 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360064623232344999) ^ 453354874410781666 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360064623232344999) ^ 59133244488362826 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360064623232344999) ^ 115249946888598 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360064623232344999) ^ 1628538 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1733994176849208167 : Nat.Prime 1733994176849208167 := by
  apply lucas_primality 1733994176849208167 (5 : ZMod 1733994176849208167)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (3454249, 1), (1300489019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (3454249, 1), (1300489019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733994176849208167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_193
      · exact prime_fiftyFiveBA_3454249
      · exact prime_fiftyFiveBA_1300489019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1733994176849208167) ^ 866997088424604083 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1733994176849208167) ^ 8984425786783462 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1733994176849208167) ^ 501988761334 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1733994176849208167) ^ 1333340114 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1977341323619550131 : Nat.Prime 1977341323619550131 := by
  apply lucas_primality 1977341323619550131 (2 : ZMod 1977341323619550131)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (1634166383156653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (1634166383156653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1977341323619550131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_1634166383156653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1977341323619550131) ^ 988670661809775065 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977341323619550131) ^ 395468264723910026 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977341323619550131) ^ 179758302147231830 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977341323619550131) ^ 1210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2143009765547021929 : Nat.Prime 2143009765547021929 := by
  apply lucas_primality 2143009765547021929 (7 : ZMod 2143009765547021929)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143009765547021929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_89292073564459247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2143009765547021929) ^ 1071504882773510964 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 714336588515673976 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 24 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2225689432678725197 : Nat.Prime 2225689432678725197 := by
  apply lucas_primality 2225689432678725197 (2 : ZMod 2225689432678725197)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (102539, 1), (414709, 1), (13084949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (102539, 1), (414709, 1), (13084949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2225689432678725197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_102539
      · exact prime_fiftyFiveBA_414709
      · exact prime_fiftyFiveBA_13084949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2225689432678725197) ^ 1112844716339362598 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2225689432678725197) ^ 21705784459364 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2225689432678725197) ^ 5366870342044 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2225689432678725197) ^ 170095384604 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2263028867053247707 : Nat.Prime 2263028867053247707 := by
  apply lucas_primality 2263028867053247707 (2 : ZMod 2263028867053247707)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (241, 1), (36467, 1), (115677223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (241, 1), (36467, 1), (115677223, 1)] : List FactorBlock).map factorBlockValue).prod) = 2263028867053247707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_241
      · exact prime_fiftyFiveBA_36467
      · exact prime_fiftyFiveBA_115677223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2263028867053247707) ^ 1131514433526623853 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 754342955684415902 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 323289838150463958 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 42698657868929202 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 9390161274079866 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 62056897113918 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2263028867053247707) ^ 19563305622 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3303983297654581211 : Nat.Prime 3303983297654581211 := by
  apply lucas_primality 3303983297654581211 (2 : ZMod 3303983297654581211)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (330398329765458121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (330398329765458121, 1)] : List FactorBlock).map factorBlockValue).prod) = 3303983297654581211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_330398329765458121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3303983297654581211) ^ 1651991648827290605 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3303983297654581211) ^ 660796659530916242 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3303983297654581211) ^ 10 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5143680382538923787 : Nat.Prime 5143680382538923787 := by
  apply lucas_primality 5143680382538923787 (5 : ZMod 5143680382538923787)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (2707, 1), (3329, 1), (552015643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (2707, 1), (3329, 1), (552015643, 1)] : List FactorBlock).map factorBlockValue).prod) = 5143680382538923787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_2707
      · exact prime_fiftyFiveBA_3329
      · exact prime_fiftyFiveBA_552015643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5143680382538923787) ^ 2571840191269461893 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5143680382538923787) ^ 467607307503538526 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5143680382538923787) ^ 109440008139126038 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5143680382538923787) ^ 1900140518115598 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5143680382538923787) ^ 1545112761351434 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5143680382538923787) ^ 9317997502 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_6675782564145480553 : Nat.Prime 6675782564145480553 := by
  apply lucas_primality 6675782564145480553 (5 : ZMod 6675782564145480553)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (241, 1), (353677, 1), (83676301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (241, 1), (353677, 1), (83676301, 1)] : List FactorBlock).map factorBlockValue).prod) = 6675782564145480553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_241
      · exact prime_fiftyFiveBA_353677
      · exact prime_fiftyFiveBA_83676301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6675782564145480553) ^ 3337891282072740276 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6675782564145480553) ^ 2225260854715160184 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6675782564145480553) ^ 513521735703498504 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6675782564145480553) ^ 27700342589815272 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6675782564145480553) ^ 18875365274376 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6675782564145480553) ^ 79781042952 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8074130727352557229 : Nat.Prime 8074130727352557229 := by
  apply lucas_primality 8074130727352557229 (2 : ZMod 8074130727352557229)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (47, 1), (89, 1), (10859, 1), (644034299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (47, 1), (89, 1), (10859, 1), (644034299, 1)] : List FactorBlock).map factorBlockValue).prod) = 8074130727352557229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_10859
      · exact prime_fiftyFiveBA_644034299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8074130727352557229) ^ 4037065363676278614 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 2691376909117519076 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 351049162058806836 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 171790015475586324 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 90720569970253452 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 743542750469892 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8074130727352557229) ^ 12536802372 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_8650830156537151507 : Nat.Prime 8650830156537151507 := by
  apply lucas_primality 8650830156537151507 (7 : ZMod 8650830156537151507)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (199, 1), (94094173862137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (199, 1), (94094173862137, 1)] : List FactorBlock).map factorBlockValue).prod) = 8650830156537151507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_199
      · exact prime_fiftyFiveBA_94094173862137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8650830156537151507) ^ 4325415078268575753 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8650830156537151507) ^ 2883610052179050502 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8650830156537151507) ^ 1235832879505307358 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8650830156537151507) ^ 786439105139741046 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8650830156537151507) ^ 43471508324307294 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8650830156537151507) ^ 91938 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_21402299406891421061 : Nat.Prime 21402299406891421061 := by
  apply lucas_primality 21402299406891421061 (2 : ZMod 21402299406891421061)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (43, 1), (59, 1), (83, 1), (10597, 1), (68509517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (43, 1), (59, 1), (83, 1), (10597, 1), (68509517, 1)] : List FactorBlock).map factorBlockValue).prod) = 21402299406891421061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_83
      · exact prime_fiftyFiveBA_10597
      · exact prime_fiftyFiveBA_68509517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21402299406891421061) ^ 10701149703445710530 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 4280459881378284212 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 3057471343841631580 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 497727893183521420 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 362750837404939340 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 257859028998691820 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 2019656450588980 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21402299406891421061) ^ 312398924180 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_28418646871883318789 : Nat.Prime 28418646871883318789 := by
  apply lucas_primality 28418646871883318789 (2 : ZMod 28418646871883318789)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod) = 28418646871883318789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_233
      · exact prime_fiftyFiveBA_30492110377557209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28418646871883318789) ^ 14209323435941659394 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 121968441510228836 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 932 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_57709978139285874797 : Nat.Prime 57709978139285874797 := by
  apply lucas_primality 57709978139285874797 (2 : ZMod 57709978139285874797)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod) = 57709978139285874797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_55379759
      · exact prime_fiftyFiveBA_260519272661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57709978139285874797) ^ 28854989069642937398 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 1042077090644 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 221519036 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_65891778720269910347 : Nat.Prime 65891778720269910347 := by
  apply lucas_primality 65891778720269910347 (2 : ZMod 65891778720269910347)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1733994176849208167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1733994176849208167, 1)] : List FactorBlock).map factorBlockValue).prod) = 65891778720269910347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_1733994176849208167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65891778720269910347) ^ 32945889360134955173 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65891778720269910347) ^ 3467988353698416334 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65891778720269910347) ^ 38 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_465140274343451881751 : Nat.Prime 465140274343451881751 := by
  apply lucas_primality 465140274343451881751 (11 : ZMod 465140274343451881751)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (939845719, 1), (1979645233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (939845719, 1), (1979645233, 1)] : List FactorBlock).map factorBlockValue).prod) = 465140274343451881751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_939845719
      · exact prime_fiftyFiveBA_1979645233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 465140274343451881751) ^ 232570137171725940875 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 465140274343451881751) ^ 93028054868690376350 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 465140274343451881751) ^ 494911308250 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (11 : ZMod 465140274343451881751) ^ 234961429750 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_558234740355005780371 : Nat.Prime 558234740355005780371 := by
  apply lucas_primality 558234740355005780371 (2 : ZMod 558234740355005780371)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod) = 558234740355005780371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_5426387
      · exact prime_fiftyFiveBA_1143045681439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558234740355005780371) ^ 279117370177502890185 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 186078246785001926790 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 111646948071001156074 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 102874111329510 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 488374830 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1079628362696274371527 : Nat.Prime 1079628362696274371527 := by
  apply lucas_primality 1079628362696274371527 (6 : ZMod 1079628362696274371527)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (1977341323619550131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (1977341323619550131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079628362696274371527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_1977341323619550131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1079628362696274371527) ^ 539814181348137185763 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079628362696274371527) ^ 359876120898758123842 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079628362696274371527) ^ 154232623242324910218 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079628362696274371527) ^ 83048335592021105502 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1079628362696274371527) ^ 546 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1118844550155768789517 : Nat.Prime 1118844550155768789517 := by
  apply lucas_primality 1118844550155768789517 (2 : ZMod 1118844550155768789517)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (151, 1), (86729, 1), (7119462691567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (151, 1), (86729, 1), (7119462691567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118844550155768789517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_151
      · exact prime_fiftyFiveBA_86729
      · exact prime_fiftyFiveBA_7119462691567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1118844550155768789517) ^ 559422275077884394758 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1118844550155768789517) ^ 372948183385256263172 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1118844550155768789517) ^ 7409566557322972116 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1118844550155768789517) ^ 12900466397119404 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1118844550155768789517) ^ 157152948 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1195732330241905885813 : Nat.Prime 1195732330241905885813 := by
  apply lucas_primality 1195732330241905885813 (2 : ZMod 1195732330241905885813)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4239269, 1), (23505080912179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4239269, 1), (23505080912179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1195732330241905885813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_4239269
      · exact prime_fiftyFiveBA_23505080912179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1195732330241905885813) ^ 597866165120952942906 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195732330241905885813) ^ 398577443413968628604 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195732330241905885813) ^ 282060970946148 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195732330241905885813) ^ 50871228 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_107
      · exact prime_fiftyFiveBA_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3349408442130034682227 : Nat.Prime 3349408442130034682227 := by
  apply lucas_primality 3349408442130034682227 (2 : ZMod 3349408442130034682227)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod) = 3349408442130034682227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_558234740355005780371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3349408442130034682227) ^ 1674704221065017341113 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 1116469480710011560742 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_4430773372276762682321 : Nat.Prime 4430773372276762682321 := by
  apply lucas_primality 4430773372276762682321 (3 : ZMod 4430773372276762682321)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod) = 4430773372276762682321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_67
      · exact prime_fiftyFiveBA_826636823185963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4430773372276762682321) ^ 2215386686138381341160 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 886154674455352536464 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 66130945854877054960 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 5360 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_6186592218418299113353 : Nat.Prime 6186592218418299113353 := by
  apply lucas_primality 6186592218418299113353 (5 : ZMod 6186592218418299113353)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (757, 1), (4093, 1), (4893884368619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (757, 1), (4093, 1), (4893884368619, 1)] : List FactorBlock).map factorBlockValue).prod) = 6186592218418299113353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_757
      · exact prime_fiftyFiveBA_4093
      · exact prime_fiftyFiveBA_4893884368619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6186592218418299113353) ^ 3093296109209149556676 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6186592218418299113353) ^ 2062197406139433037784 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6186592218418299113353) ^ 363917189318723477256 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6186592218418299113353) ^ 8172512838069087336 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6186592218418299113353) ^ 1511505550554189864 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6186592218418299113353) ^ 1264147608 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_6220227526635449599897 : Nat.Prime 6220227526635449599897 := by
  apply lucas_primality 6220227526635449599897 (10 : ZMod 6220227526635449599897)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (541727, 1), (2830921604983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (541727, 1), (2830921604983, 1)] : List FactorBlock).map factorBlockValue).prod) = 6220227526635449599897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_541727
      · exact prime_fiftyFiveBA_2830921604983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6220227526635449599897) ^ 3110113763317724799948 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6220227526635449599897) ^ 2073409175545149866632 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6220227526635449599897) ^ 478479040510419199992 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6220227526635449599897) ^ 11482218029811048 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6220227526635449599897) ^ 2197244712 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_11765822802965820719843 : Nat.Prime 11765822802965820719843 := by
  apply lucas_primality 11765822802965820719843 (2 : ZMod 11765822802965820719843)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1103, 1), (4679, 1), (1139892116777033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1103, 1), (4679, 1), (1139892116777033, 1)] : List FactorBlock).map factorBlockValue).prod) = 11765822802965820719843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_1103
      · exact prime_fiftyFiveBA_4679
      · exact prime_fiftyFiveBA_1139892116777033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11765822802965820719843) ^ 5882911401482910359921 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11765822802965820719843) ^ 10667110428799474814 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11765822802965820719843) ^ 2514602009610134798 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11765822802965820719843) ^ 10321874 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_13667492001383723426423 : Nat.Prime 13667492001383723426423 := by
  apply lucas_primality 13667492001383723426423 (5 : ZMod 13667492001383723426423)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (641, 1), (62549, 1), (941676771059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (641, 1), (62549, 1), (941676771059, 1)] : List FactorBlock).map factorBlockValue).prod) = 13667492001383723426423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_181
      · exact prime_fiftyFiveBA_641
      · exact prime_fiftyFiveBA_62549
      · exact prime_fiftyFiveBA_941676771059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13667492001383723426423) ^ 6833746000691861713211 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13667492001383723426423) ^ 75511005532506759262 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13667492001383723426423) ^ 21322140407774919542 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13667492001383723426423) ^ 218508561310072478 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13667492001383723426423) ^ 14513995058 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_14845898385209239665497 : Nat.Prime 14845898385209239665497 := by
  apply lucas_primality 14845898385209239665497 (3 : ZMod 14845898385209239665497)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (62762281, 1), (29567715968627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (62762281, 1), (29567715968627, 1)] : List FactorBlock).map factorBlockValue).prod) = 14845898385209239665497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_62762281
      · exact prime_fiftyFiveBA_29567715968627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14845898385209239665497) ^ 7422949192604619832748 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14845898385209239665497) ^ 236541727749016 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14845898385209239665497) ^ 502098248 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_16281605594754210944329 : Nat.Prime 16281605594754210944329 := by
  apply lucas_primality 16281605594754210944329 (7 : ZMod 16281605594754210944329)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (1049, 1), (581351, 1), (4654512227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (1049, 1), (581351, 1), (4654512227, 1)] : List FactorBlock).map factorBlockValue).prod) = 16281605594754210944329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_239
      · exact prime_fiftyFiveBA_1049
      · exact prime_fiftyFiveBA_581351
      · exact prime_fiftyFiveBA_4654512227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16281605594754210944329) ^ 8140802797377105472164 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16281605594754210944329) ^ 5427201864918070314776 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16281605594754210944329) ^ 68123872781398372152 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16281605594754210944329) ^ 15521073016924891272 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16281605594754210944329) ^ 28006497958641528 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16281605594754210944329) ^ 3498026173464 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_22072694329998416363551 : Nat.Prime 22072694329998416363551 := by
  apply lucas_primality 22072694329998416363551 (3 : ZMod 22072694329998416363551)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (41, 1), (317, 1), (541, 1), (20927806250941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (41, 1), (317, 1), (541, 1), (20927806250941, 1)] : List FactorBlock).map factorBlockValue).prod) = 22072694329998416363551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_317
      · exact prime_fiftyFiveBA_541
      · exact prime_fiftyFiveBA_20927806250941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22072694329998416363551) ^ 11036347164999208181775 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 7357564776666138787850 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 4414538865999683272710 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 538358398292644301550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 69629950567818348150 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 40799804676522026550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22072694329998416363551) ^ 1054706550 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_57110078409302094014171 : Nat.Prime 57110078409302094014171 := by
  apply lucas_primality 57110078409302094014171 (6 : ZMod 57110078409302094014171)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod) = 57110078409302094014171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_21160721
      · exact prime_fiftyFiveBA_269887204737977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57110078409302094014171) ^ 28555039204651047007085 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 11422015681860418802834 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 2698872047379770 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 211607210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_67024695540586320517363 : Nat.Prime 67024695540586320517363 := by
  apply lucas_primality 67024695540586320517363 (3 : ZMod 67024695540586320517363)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod) = 67024695540586320517363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_1899647
      · exact prime_fiftyFiveBA_2909674311721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67024695540586320517363) ^ 33512347770293160258681 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 22341565180195440172454 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1558713849781077221334 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1426057351927368521646 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 35282710703928846 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 23035119522 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_91559036862681499298959 : Nat.Prime 91559036862681499298959 := by
  apply lucas_primality 91559036862681499298959 (6 : ZMod 91559036862681499298959)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (21402299406891421061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (21402299406891421061, 1)] : List FactorBlock).map factorBlockValue).prod) = 91559036862681499298959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_21402299406891421061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 91559036862681499298959) ^ 45779518431340749649479 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 91559036862681499298959) ^ 30519678954227166432986 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 91559036862681499298959) ^ 3980827689681804317346 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 91559036862681499298959) ^ 2953517318151016106418 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (6 : ZMod 91559036862681499298959) ^ 4278 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_614861506554349437030163 : Nat.Prime 614861506554349437030163 := by
  apply lucas_primality 614861506554349437030163 (3 : ZMod 614861506554349437030163)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod) = 614861506554349437030163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_29304298123
      · exact prime_fiftyFiveBA_3496992739049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614861506554349437030163) ^ 307430753277174718515081 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 204953835518116479010054 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 20981956434294 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 175825788738 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1265391609271901934596783 : Nat.Prime 1265391609271901934596783 := by
  apply lucas_primality 1265391609271901934596783 (5 : ZMod 1265391609271901934596783)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (132113, 1), (229518851, 1), (20865607757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (132113, 1), (229518851, 1), (20865607757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1265391609271901934596783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_132113
      · exact prime_fiftyFiveBA_229518851
      · exact prime_fiftyFiveBA_20865607757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1265391609271901934596783) ^ 632695804635950967298391 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1265391609271901934596783) ^ 9578100635606654414 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1265391609271901934596783) ^ 5513236075201082 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1265391609271901934596783) ^ 60644847924326 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1628711517524677505087789 : Nat.Prime 1628711517524677505087789 := by
  apply lucas_primality 1628711517524677505087789 (2 : ZMod 1628711517524677505087789)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2591, 1), (1648045081, 1), (95355923357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2591, 1), (1648045081, 1), (95355923357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1628711517524677505087789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_2591
      · exact prime_fiftyFiveBA_1648045081
      · exact prime_fiftyFiveBA_95355923357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1628711517524677505087789) ^ 814355758762338752543894 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1628711517524677505087789) ^ 628603441730867427668 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1628711517524677505087789) ^ 988268789671948 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1628711517524677505087789) ^ 17080339219484 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1978659240655303067678693 : Nat.Prime 1978659240655303067678693 := by
  apply lucas_primality 1978659240655303067678693 (2 : ZMod 1978659240655303067678693)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3911, 1), (6451, 1), (8316337, 1), (2357567189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3911, 1), (6451, 1), (8316337, 1), (2357567189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1978659240655303067678693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3911
      · exact prime_fiftyFiveBA_6451
      · exact prime_fiftyFiveBA_8316337
      · exact prime_fiftyFiveBA_2357567189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1978659240655303067678693) ^ 989329620327651533839346 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978659240655303067678693) ^ 505921564984736146172 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978659240655303067678693) ^ 306721320827050545292 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978659240655303067678693) ^ 237924369906522916 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978659240655303067678693) ^ 839280106156628 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2554495330019847759305633 : Nat.Prime 2554495330019847759305633 := by
  apply lucas_primality 2554495330019847759305633 (3 : ZMod 2554495330019847759305633)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554495330019847759305633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_28418646871883318789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2554495330019847759305633) ^ 1277247665009923879652816 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 48198025094714108666144 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 89888 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2724459656666326924754887 : Nat.Prime 2724459656666326924754887 := by
  apply lucas_primality 2724459656666326924754887 (3 : ZMod 2724459656666326924754887)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (6220227526635449599897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (6220227526635449599897, 1)] : List FactorBlock).map factorBlockValue).prod) = 2724459656666326924754887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_73
      · exact prime_fiftyFiveBA_6220227526635449599897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2724459656666326924754887) ^ 1362229828333163462377443 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2724459656666326924754887) ^ 908153218888775641584962 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2724459656666326924754887) ^ 37321365159812697599382 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2724459656666326924754887) ^ 438 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3335625250110558362220421 : Nat.Prime 3335625250110558362220421 := by
  apply lucas_primality 3335625250110558362220421 (2 : ZMod 3335625250110558362220421)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1861, 1), (9599189, 1), (3112039398583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1861, 1), (9599189, 1), (3112039398583, 1)] : List FactorBlock).map factorBlockValue).prod) = 3335625250110558362220421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_1861
      · exact prime_fiftyFiveBA_9599189
      · exact prime_fiftyFiveBA_3112039398583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3335625250110558362220421) ^ 1667812625055279181110210 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335625250110558362220421) ^ 1111875083370186120740140 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335625250110558362220421) ^ 667125050022111672444084 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335625250110558362220421) ^ 1792383261746672951220 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335625250110558362220421) ^ 347490319245777780 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335625250110558362220421) ^ 1071845443740 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5698920124947872455138027 : Nat.Prime 5698920124947872455138027 := by
  apply lucas_primality 5698920124947872455138027 (2 : ZMod 5698920124947872455138027)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5698920124947872455138027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_89
      · exact prime_fiftyFiveBA_1217
      · exact prime_fiftyFiveBA_974357259695558663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5698920124947872455138027) ^ 2849460062473936227569013 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 1899640041649290818379342 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 64032810392672724215034 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 4682760990096854934378 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 5848902 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_18117770583910622656206433 : Nat.Prime 18117770583910622656206433 := by
  apply lucas_primality 18117770583910622656206433 (5 : ZMod 18117770583910622656206433)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (36691, 1), (5143680382538923787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (36691, 1), (5143680382538923787, 1)] : List FactorBlock).map factorBlockValue).prod) = 18117770583910622656206433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_36691
      · exact prime_fiftyFiveBA_5143680382538923787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18117770583910622656206433) ^ 9058885291955311328103216 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18117770583910622656206433) ^ 6039256861303540885402144 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18117770583910622656206433) ^ 493793316723736683552 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18117770583910622656206433) ^ 3522336 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_60041254501990050519967579 : Nat.Prime 60041254501990050519967579 := by
  apply lucas_primality 60041254501990050519967579 (2 : ZMod 60041254501990050519967579)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3335625250110558362220421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3335625250110558362220421, 1)] : List FactorBlock).map factorBlockValue).prod) = 60041254501990050519967579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_3335625250110558362220421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60041254501990050519967579) ^ 30020627250995025259983789 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 60041254501990050519967579) ^ 20013751500663350173322526 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 60041254501990050519967579) ^ 18 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_124807444578992753767994027 : Nat.Prime 124807444578992753767994027 := by
  apply lucas_primality 124807444578992753767994027 (2 : ZMod 124807444578992753767994027)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (109097, 1), (2225689432678725197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (109097, 1), (2225689432678725197, 1)] : List FactorBlock).map factorBlockValue).prod) = 124807444578992753767994027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_257
      · exact prime_fiftyFiveBA_109097
      · exact prime_fiftyFiveBA_2225689432678725197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124807444578992753767994027) ^ 62403722289496376883997013 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 124807444578992753767994027) ^ 485632080073901765634218 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 124807444578992753767994027) ^ 1144004368396864751258 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 124807444578992753767994027) ^ 56075858 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_200693452548318594793595333 : Nat.Prime 200693452548318594793595333 := by
  apply lucas_primality 200693452548318594793595333 (2 : ZMod 200693452548318594793595333)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3671, 1), (13667492001383723426423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3671, 1), (13667492001383723426423, 1)] : List FactorBlock).map factorBlockValue).prod) = 200693452548318594793595333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3671
      · exact prime_fiftyFiveBA_13667492001383723426423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 200693452548318594793595333) ^ 100346726274159297396797666 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 200693452548318594793595333) ^ 54669968005534893705692 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 200693452548318594793595333) ^ 14684 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_401386905096637189587190667 : Nat.Prime 401386905096637189587190667 := by
  apply lucas_primality 401386905096637189587190667 (2 : ZMod 401386905096637189587190667)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (200693452548318594793595333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (200693452548318594793595333, 1)] : List FactorBlock).map factorBlockValue).prod) = 401386905096637189587190667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_200693452548318594793595333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 401386905096637189587190667) ^ 200693452548318594793595333 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 401386905096637189587190667) ^ 2 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_747410099145462353024424001 : Nat.Prime 747410099145462353024424001 := by
  apply lucas_primality 747410099145462353024424001 (89 : ZMod 747410099145462353024424001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 747410099145462353024424001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 747410099145462353024424001) ^ 373705049572731176512212000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 249136699715154117674808000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 149482019829092470604884800 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 106772871306494621860632000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 67946372649587486638584000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 57493084549650950232648000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 43965299949733079589672000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 39337373639234860685496000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 32496091267194015348888000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 24110003198240721065304000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 20200272949877360892552000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 18229514613303959829864000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 17381630212685171000568000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 15902342535009837298392000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 14102077342367214208008000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 12667967782126480559736000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (89 : ZMod 747410099145462353024424001) ^ 12252624576155120541384000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1226880728785947636096696001 : Nat.Prime 1226880728785947636096696001 := by
  apply lucas_primality 1226880728785947636096696001 (83 : ZMod 1226880728785947636096696001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226880728785947636096696001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1226880728785947636096696001) ^ 613440364392973818048348000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 408960242928649212032232000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 245376145757189527219339200 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 175268675540849662299528000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 111534611707813421463336000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 94375440675842125853592000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 72169454634467508005688000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 64572669936102507162984000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 53342640381997723308552000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 42306232027101642624024000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 39576797702772504390216000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 33158938615836422597208000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 29923920214291405758456000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 28532109971766224095272000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 26103845293318034810568000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 20794588623490637899944000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (83 : ZMod 1226880728785947636096696001) ^ 20112798832556518624536000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_1585967771357444505198168001 : Nat.Prime 1585967771357444505198168001 := by
  apply lucas_primality 1585967771357444505198168001 (41 : ZMod 1585967771357444505198168001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585967771357444505198168001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 1585967771357444505198168001) ^ 792983885678722252599084000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 528655923785814835066056000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 317193554271488901039633600 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 226566824479634929314024000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 144178888305222227745288000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 121997520873649577322936000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 93292221844555559129304000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 83471987966181289747272000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 68955120493801935008616000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 54688543839911879489592000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 51160250688949822748328000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 42863993820471473113464000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 36882971426917314074376000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 33743995135264776706344000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 29923920214291405758456000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 26880809684024483138952000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (41 : ZMod 1585967771357444505198168001) ^ 25999471661597450904888000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2322309950916258025468746001 : Nat.Prime 2322309950916258025468746001 := by
  apply lucas_primality 2322309950916258025468746001 (97 : ZMod 2322309950916258025468746001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2322309950916258025468746001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 2322309950916258025468746001) ^ 1161154975458129012734373000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 774103316972086008489582000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 464461990183251605093749200 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 331758564416608289352678000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 211119086446932547769886000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 178639226993558309651442000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 136606467700956354439338000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 122226839521908317129934000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 100969997865924261976902000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 80079653479870966395474000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 74913224223105097595766000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 62765133808547514201858000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 56641706119908732328506000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 54007208160843209894622000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 49410850019494851605718000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 43817168885212415574882000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 39361185608750136024894000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (97 : ZMod 2322309950916258025468746001) ^ 38070654933053410253586000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_2408321430579823137523144003 : Nat.Prime 2408321430579823137523144003 := by
  apply lucas_primality 2408321430579823137523144003 (2 : ZMod 2408321430579823137523144003)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (401386905096637189587190667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (401386905096637189587190667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2408321430579823137523144003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_401386905096637189587190667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2408321430579823137523144003) ^ 1204160715289911568761572001 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2408321430579823137523144003) ^ 802773810193274379174381334 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2408321430579823137523144003) ^ 6 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_3824981095626777924301464001 : Nat.Prime 3824981095626777924301464001 := by
  apply lucas_primality 3824981095626777924301464001 (34 : ZMod 3824981095626777924301464001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3824981095626777924301464001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 3824981095626777924301464001) ^ 1912490547813388962150732000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 1274993698542259308100488000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 764996219125355584860292800 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 546425870803825417757352000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 347725554147888902209224000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 294229315048213686484728000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 201314794506672522331656000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 166303525896816431491368000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 131895899849199238769016000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 123386486955702513687144000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 103377867449372376332472000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 93292221844555559129304000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 88953048735506463355848000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 81382576502697402644712000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 72169454634467508005688000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 64830188061470812276296000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (34 : ZMod 3824981095626777924301464001) ^ 62704608125029146300024000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_5418723218804602059427074001 : Nat.Prime 5418723218804602059427074001 := by
  apply lucas_primality 5418723218804602059427074001 (71 : ZMod 5418723218804602059427074001)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 5418723218804602059427074001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_5
      · exact prime_fiftyFiveBA_7
      · exact prime_fiftyFiveBA_11
      · exact prime_fiftyFiveBA_13
      · exact prime_fiftyFiveBA_17
      · exact prime_fiftyFiveBA_19
      · exact prime_fiftyFiveBA_23
      · exact prime_fiftyFiveBA_29
      · exact prime_fiftyFiveBA_31
      · exact prime_fiftyFiveBA_37
      · exact prime_fiftyFiveBA_41
      · exact prime_fiftyFiveBA_43
      · exact prime_fiftyFiveBA_47
      · exact prime_fiftyFiveBA_53
      · exact prime_fiftyFiveBA_59
      · exact prime_fiftyFiveBA_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 5418723218804602059427074001) ^ 2709361609402301029713537000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 1806241072934867353142358000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 1083744643760920411885414800 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 774103316972086008489582000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 492611201709509278129734000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 416824862984969389186698000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 318748424635564827025122000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 285195958884452739969846000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 235596661687156611279438000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 186852524786365588256106000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 174797523187245227723454000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 146451978886610866471002000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 132163980946453708766514000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 126016819041967489754118000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 115291983378821320413342000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 102240060732162303008058000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 91842766420416984058086000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (71 : ZMod 5418723218804602059427074001) ^ 88831528177124623925034000 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem prime_fiftyFiveBA_65024678625655224713124888073 : Nat.Prime 65024678625655224713124888073 := by
  apply lucas_primality 65024678625655224713124888073 (5 : ZMod 65024678625655224713124888073)
  · rw [← fiftyFiveBAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (127, 1), (479, 1), (14845898385209239665497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (127, 1), (479, 1), (14845898385209239665497, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFiveBA_2
      · exact prime_fiftyFiveBA_3
      · exact prime_fiftyFiveBA_127
      · exact prime_fiftyFiveBA_479
      · exact prime_fiftyFiveBA_14845898385209239665497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 65024678625655224713124888073) ^ 32512339312827612356562444036 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 65024678625655224713124888073) ^ 21674892875218408237708296024 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 65024678625655224713124888073) ^ 512005343509096257583660536 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 65024678625655224713124888073) ^ 135750894834353287501304568 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide
    · change (5 : ZMod 65024678625655224713124888073) ^ 4379976 ≠ 1
      rw [← fiftyFiveBAFastPow_eq_pow]
      decide

private theorem phi_fiftyFiveBA_65024678625655224713124888000 : Nat.totient 65024678625655224713124888000 = 8556425265264835166208000000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 3), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_7, prime_fiftyFiveBA_11, prime_fiftyFiveBA_13, prime_fiftyFiveBA_17, prime_fiftyFiveBA_19, prime_fiftyFiveBA_23, prime_fiftyFiveBA_29, prime_fiftyFiveBA_31, prime_fiftyFiveBA_37, prime_fiftyFiveBA_41, prime_fiftyFiveBA_43, prime_fiftyFiveBA_47, prime_fiftyFiveBA_53, prime_fiftyFiveBA_59, prime_fiftyFiveBA_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888001 : Nat.totient 65024678625655224713124888001 = 64559085426457885078152043840 := by
  rw [← show ((([(149, 1), (2213, 1), (553087763, 1), (356546750101571, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_149, prime_fiftyFiveBA_2213, prime_fiftyFiveBA_553087763, prime_fiftyFiveBA_356546750101571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888002 : Nat.totient 65024678625655224713124888002 = 32445574501986167165556596880 := by
  rw [← show ((([(2, 1), (491, 1), (59183, 1), (1118844550155768789517, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_491, prime_fiftyFiveBA_59183, prime_fiftyFiveBA_1118844550155768789517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888003 : Nat.totient 65024678625655224713124888003 = 43349783358972155991568566624 := by
  rw [← show ((([(3, 1), (18126877, 1), (1195732330241905885813, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_18126877, prime_fiftyFiveBA_1195732330241905885813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888004 : Nat.totient 65024678625655224713124888004 = 32275022967465521475135005760 := by
  rw [← show ((([(2, 2), (137, 1), (2630685188203, 1), (45105424703291, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_137, prime_fiftyFiveBA_2630685188203, prime_fiftyFiveBA_45105424703291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888005 : Nat.totient 65024678625655224713124888005 = 51392941596229060467315850240 := by
  rw [← show ((([(5, 1), (83, 1), (895529, 1), (2064319931, 1), (84756586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_83, prime_fiftyFiveBA_895529, prime_fiftyFiveBA_2064319931, prime_fiftyFiveBA_84756586553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888006 : Nat.totient 65024678625655224713124888006 = 21613208350252417554347028480 := by
  rw [← show ((([(2, 1), (3, 1), (353, 1), (85931, 1), (747277, 1), (15018779, 1), (31833629, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_353, prime_fiftyFiveBA_85931, prime_fiftyFiveBA_747277, prime_fiftyFiveBA_15018779, prime_fiftyFiveBA_31833629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888007 : Nat.totient 65024678625655224713124888007 = 55731009146655533889029011488 := by
  rw [← show ((([(7, 1), (13109, 1), (313127, 1), (2263028867053247707, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_7, prime_fiftyFiveBA_13109, prime_fiftyFiveBA_313127, prime_fiftyFiveBA_2263028867053247707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888008 : Nat.totient 65024678625655224713124888008 = 32452520542317087476364172800 := by
  rw [← show ((([(2, 3), (547, 1), (85193, 1), (112850341, 1), (1545589339391, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_547, prime_fiftyFiveBA_85193, prime_fiftyFiveBA_112850341, prime_fiftyFiveBA_1545589339391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888009 : Nat.totient 65024678625655224713124888009 = 43218529045905495202783948800 := by
  rw [← show ((([(3, 2), (331, 1), (149057, 1), (67937963, 1), (2155474125481, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_331, prime_fiftyFiveBA_149057, prime_fiftyFiveBA_67937963, prime_fiftyFiveBA_2155474125481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888010 : Nat.totient 65024678625655224713124888010 = 26009869129425253958775645888 := by
  rw [← show ((([(2, 1), (5, 1), (11218483, 1), (15837208853, 1), (36598681199, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_11218483, prime_fiftyFiveBA_15837208853, prime_fiftyFiveBA_36598681199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888011 : Nat.totient 65024678625655224713124888011 = 59112932745743805527241105120 := by
  rw [← show ((([(11, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_11, prime_fiftyFiveBA_143669, prime_fiftyFiveBA_13852339783, prime_fiftyFiveBA_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888012 : Nat.totient 65024678625655224713124888012 = 21674892875218408237708296000 := by
  rw [← show ((([(2, 2), (3, 1), (5418723218804602059427074001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5418723218804602059427074001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888013 : Nat.totient 65024678625655224713124888013 = 59126917877734807194888790656 := by
  rw [← show ((([(13, 1), (67, 1), (8595391086979, 1), (8685491862457, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_13, prime_fiftyFiveBA_67, prime_fiftyFiveBA_8595391086979, prime_fiftyFiveBA_8685491862457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888014 : Nat.totient 65024678625655224713124888014 = 27849142274905942351576180224 := by
  rw [← show ((([(2, 1), (7, 1), (1583, 1), (28703, 1), (11233337, 1), (9099828029177, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_7, prime_fiftyFiveBA_1583, prime_fiftyFiveBA_28703, prime_fiftyFiveBA_11233337, prime_fiftyFiveBA_9099828029177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888015 : Nat.totient 65024678625655224713124888015 = 34659392637709294398258814976 := by
  rw [← show ((([(3, 1), (5, 1), (1697, 1), (2554495330019847759305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_1697, prime_fiftyFiveBA_2554495330019847759305633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888016 : Nat.totient 65024678625655224713124888016 = 32512339312823896697930582016 := by
  rw [← show ((([(2, 4), (8921454134557, 1), (455535874848193, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_8921454134557, prime_fiftyFiveBA_455535874848193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888017 : Nat.totient 65024678625655224713124888017 = 61199697530028446788823424000 := by
  rw [← show ((([(17, 1), (3824981095626777924301464001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_17, prime_fiftyFiveBA_3824981095626777924301464001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888018 : Nat.totient 65024678625655224713124888018 = 21582003274511992446234016896 := by
  rw [← show ((([(2, 1), (3, 2), (239, 1), (9839, 1), (3637709, 1), (422307596157509, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_239, prime_fiftyFiveBA_9839, prime_fiftyFiveBA_3637709, prime_fiftyFiveBA_422307596157509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888019 : Nat.totient 65024678625655224713124888019 = 61520299826786621337465000000 := by
  rw [← show ((([(19, 1), (751, 1), (272794601, 1), (16705093306204151, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_19, prime_fiftyFiveBA_751, prime_fiftyFiveBA_272794601, prime_fiftyFiveBA_16705093306204151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888020 : Nat.totient 65024678625655224713124888020 = 26003694454464941181141429120 := by
  rw [← show ((([(2, 2), (5, 1), (4211, 1), (75111599, 1), (10279120799235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_4211, prime_fiftyFiveBA_75111599, prime_fiftyFiveBA_10279120799235109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888021 : Nat.totient 65024678625655224713124888021 = 37141774515348865584284745264 := by
  rw [← show ((([(3, 1), (7, 1), (2447, 1), (1265391609271901934596783, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_7, prime_fiftyFiveBA_2447, prime_fiftyFiveBA_1265391609271901934596783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888022 : Nat.totient 65024678625655224713124888022 = 29418085757912264598150743040 := by
  rw [← show ((([(2, 1), (11, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_11, prime_fiftyFiveBA_223, prime_fiftyFiveBA_5113, prime_fiftyFiveBA_101287, prime_fiftyFiveBA_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888023 : Nat.totient 65024678625655224713124888023 = 61282577760068574007443899136 := by
  rw [← show ((([(23, 1), (109, 1), (179, 1), (1650287, 1), (87803407596954793, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_23, prime_fiftyFiveBA_109, prime_fiftyFiveBA_179, prime_fiftyFiveBA_1650287, prime_fiftyFiveBA_87803407596954793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888024 : Nat.totient 65024678625655224713124888024 = 21596572126394341251791938560 := by
  rw [← show ((([(2, 3), (3, 1), (277, 1), (368791, 1), (1602427, 1), (16551167573209, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_277, prime_fiftyFiveBA_368791, prime_fiftyFiveBA_1602427, prime_fiftyFiveBA_16551167573209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888025 : Nat.totient 65024678625655224713124888025 = 51893310288276629476873632000 := by
  rw [← show ((([(5, 2), (631, 1), (1181, 1), (3446959, 1), (1012564812501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_631, prime_fiftyFiveBA_1181, prime_fiftyFiveBA_3446959, prime_fiftyFiveBA_1012564812501629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888026 : Nat.totient 65024678625655224713124888026 = 30011218481475983083038651648 := by
  rw [← show ((([(2, 1), (13, 1), (185483, 1), (3374797, 1), (54756067, 1), (72966053, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_13, prime_fiftyFiveBA_185483, prime_fiftyFiveBA_3374797, prime_fiftyFiveBA_54756067, prime_fiftyFiveBA_72966053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888027 : Nat.totient 65024678625655224713124888027 = 43349783105815233792325368480 := by
  rw [← show ((([(3, 3), (16491773, 1), (2851043827, 1), (51220428631, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_16491773, prime_fiftyFiveBA_2851043827, prime_fiftyFiveBA_51220428631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888028 : Nat.totient 65024678625655224713124888028 = 27867719410995096305624952000 := by
  rw [← show ((([(2, 2), (7, 1), (2322309950916258025468746001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_7, prime_fiftyFiveBA_2322309950916258025468746001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888029 : Nat.totient 65024678625655224713124888029 = 62706163457832180500158456176 := by
  rw [← show ((([(29, 1), (823, 1), (2724459656666326924754887, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_29, prime_fiftyFiveBA_823, prime_fiftyFiveBA_2724459656666326924754887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888030 : Nat.totient 65024678625655224713124888030 = 17339914297179711992819367936 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (5789592673, 1), (374376818878815937, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_5789592673, prime_fiftyFiveBA_374376818878815937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888031 : Nat.totient 65024678625655224713124888031 = 62596618848607940193167280000 := by
  rw [← show ((([(31, 1), (317, 1), (691, 1), (1523, 1), (847031, 1), (7423009264091, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_31, prime_fiftyFiveBA_317, prime_fiftyFiveBA_691, prime_fiftyFiveBA_1523, prime_fiftyFiveBA_847031, prime_fiftyFiveBA_7423009264091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888032 : Nat.totient 65024678625655224713124888032 = 32455339131419475659530122240 := by
  rw [← show ((([(2, 5), (571, 1), (533077, 1), (6675782564145480553, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_571, prime_fiftyFiveBA_533077, prime_fiftyFiveBA_6675782564145480553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888033 : Nat.totient 65024678625655224713124888033 = 38869044848683910814036672000 := by
  rw [← show ((([(3, 1), (11, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_11, prime_fiftyFiveBA_73, prime_fiftyFiveBA_13737811, prime_fiftyFiveBA_68784581, prime_fiftyFiveBA_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888034 : Nat.totient 65024678625655224713124888034 = 30526796002663632195451530240 := by
  rw [← show ((([(2, 1), (17, 1), (419, 1), (1381489, 1), (3303983297654581211, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_17, prime_fiftyFiveBA_419, prime_fiftyFiveBA_1381489, prime_fiftyFiveBA_3303983297654581211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888035 : Nat.totient 65024678625655224713124888035 = 44586980415710330838742802400 := by
  rw [← show ((([(5, 1), (7, 1), (32531, 1), (57110078409302094014171, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_7, prime_fiftyFiveBA_32531, prime_fiftyFiveBA_57110078409302094014171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888036 : Nat.totient 65024678625655224713124888036 = 21655348337008112107647229248 := by
  rw [← show ((([(2, 2), (3, 2), (1109, 1), (1628711517524677505087789, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_1109, prime_fiftyFiveBA_1628711517524677505087789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888037 : Nat.totient 65024678625655224713124888037 = 62615015137995111899849428992 := by
  rw [← show ((([(37, 1), (97, 1), (18117770583910622656206433, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_37, prime_fiftyFiveBA_97, prime_fiftyFiveBA_18117770583910622656206433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888038 : Nat.totient 65024678625655224713124888038 = 30651967409981933092041296640 := by
  rw [← show ((([(2, 1), (19, 1), (311, 1), (617, 1), (77267, 1), (115413075534405269, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_19, prime_fiftyFiveBA_311, prime_fiftyFiveBA_617, prime_fiftyFiveBA_77267, prime_fiftyFiveBA_115413075534405269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888039 : Nat.totient 65024678625655224713124888039 = 40014904466809790182222330848 := by
  rw [← show ((([(3, 1), (13, 1), (141707, 1), (11765822802965820719843, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_13, prime_fiftyFiveBA_141707, prime_fiftyFiveBA_11765822802965820719843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888040 : Nat.totient 65024678625655224713124888040 = 25978731146058131226759333888 := by
  rw [← show ((([(2, 3), (5, 1), (857, 1), (32869, 1), (57709978139285874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_857, prime_fiftyFiveBA_32869, prime_fiftyFiveBA_57709978139285874797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888041 : Nat.totient 65024678625655224713124888041 = 63438710854297780207926720000 := by
  rw [← show ((([(41, 1), (1585967771357444505198168001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_41, prime_fiftyFiveBA_1585967771357444505198168001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888042 : Nat.totient 65024678625655224713124888042 = 18404062977801957286638001152 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (107, 1), (23417, 1), (1025159417, 1), (602729551187, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_7, prime_fiftyFiveBA_107, prime_fiftyFiveBA_23417, prime_fiftyFiveBA_1025159417, prime_fiftyFiveBA_602729551187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888043 : Nat.totient 65024678625655224713124888043 = 63440056638977802780140708256 := by
  rw [← show ((([(43, 1), (877, 1), (28972335619, 1), (59515030159927, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_43, prime_fiftyFiveBA_877, prime_fiftyFiveBA_28972335619, prime_fiftyFiveBA_59515030159927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888044 : Nat.totient 65024678625655224713124888044 = 29556672102570556687784040000 := by
  rw [← show ((([(2, 2), (11, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_11, prime_fiftyFiveBA_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888045 : Nat.totient 65024678625655224713124888045 = 34336462631113817514644889600 := by
  rw [← show ((([(3, 2), (5, 1), (101, 1), (25824109, 1), (554011756364663489, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_101, prime_fiftyFiveBA_25824109, prime_fiftyFiveBA_554011756364663489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888046 : Nat.totient 65024678625655224713124888046 = 31096745043893693695900899288 := by
  rw [← show ((([(2, 1), (23, 1), (15439, 1), (91559036862681499298959, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_23, prime_fiftyFiveBA_15439, prime_fiftyFiveBA_91559036862681499298959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888047 : Nat.totient 65024678625655224713124888047 = 63641125162204684839484746552 := by
  rw [← show ((([(47, 1), (1281463, 1), (1079628362696274371527, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_47, prime_fiftyFiveBA_1281463, prime_fiftyFiveBA_1079628362696274371527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888048 : Nat.totient 65024678625655224713124888048 = 21674884926510609258197191680 := by
  rw [← show ((([(2, 4), (3, 1), (3780509, 1), (9783821, 1), (36625047980509, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_3780509, prime_fiftyFiveBA_9783821, prime_fiftyFiveBA_36625047980509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888049 : Nat.totient 65024678625655224713124888049 = 55620815754957583174210194336 := by
  rw [← show ((([(7, 2), (487, 1), (314989, 1), (8650830156537151507, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_7, prime_fiftyFiveBA_487, prime_fiftyFiveBA_314989, prime_fiftyFiveBA_8650830156537151507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888050 : Nat.totient 65024678625655224713124888050 = 25642820607537892703603366400 := by
  rw [← show ((([(2, 1), (5, 2), (71, 1), (37967, 1), (834527, 1), (3072847, 1), (188131817, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_71, prime_fiftyFiveBA_37967, prime_fiftyFiveBA_834527, prime_fiftyFiveBA_3072847, prime_fiftyFiveBA_188131817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888051 : Nat.totient 65024678625655224713124888051 = 40597699725817484369745862656 := by
  rw [← show ((([(3, 1), (17, 1), (307, 1), (593, 1), (65269, 1), (107302047888098879, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_17, prime_fiftyFiveBA_307, prime_fiftyFiveBA_593, prime_fiftyFiveBA_65269, prime_fiftyFiveBA_107302047888098879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888052 : Nat.totient 65024678625655224713124888052 = 29594961895525325470740602880 := by
  rw [← show ((([(2, 2), (13, 1), (89, 1), (953, 1), (967, 1), (1699, 1), (8973711654617341, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_13, prime_fiftyFiveBA_89, prime_fiftyFiveBA_953, prime_fiftyFiveBA_967, prime_fiftyFiveBA_1699, prime_fiftyFiveBA_8973711654617341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888053 : Nat.totient 65024678625655224713124888053 = 63797797896869277077028192000 := by
  rw [← show ((([(53, 1), (1226880728785947636096696001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_53, prime_fiftyFiveBA_1226880728785947636096696001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888054 : Nat.totient 65024678625655224713124888054 = 21674892875218408237708295964 := by
  rw [← show ((([(2, 1), (3, 4), (401386905096637189587190667, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_401386905096637189587190667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888055 : Nat.totient 65024678625655224713124888055 = 46822193114131825580039047680 := by
  rw [← show ((([(5, 1), (11, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_11, prime_fiftyFiveBA_103, prime_fiftyFiveBA_5009, prime_fiftyFiveBA_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888056 : Nat.totient 65024678625655224713124888056 = 27859056767120406886079938560 := by
  rw [← show ((([(2, 3), (7, 1), (3217, 1), (15113094193, 1), (23882827256521, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_7, prime_fiftyFiveBA_3217, prime_fiftyFiveBA_15113094193, prime_fiftyFiveBA_23882827256521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888057 : Nat.totient 65024678625655224713124888057 = 41068218079361194555657823352 := by
  rw [← show ((([(3, 1), (19, 2), (60041254501990050519967579, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_19, prime_fiftyFiveBA_60041254501990050519967579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888058 : Nat.totient 65024678625655224713124888058 = 30831592988264920820554622400 := by
  rw [← show ((([(2, 1), (29, 1), (79, 1), (191, 1), (13100239, 1), (5671664637949631, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_29, prime_fiftyFiveBA_79, prime_fiftyFiveBA_191, prime_fiftyFiveBA_13100239, prime_fiftyFiveBA_5671664637949631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888059 : Nat.totient 65024678625655224713124888059 = 63807803192652213326502459616 := by
  rw [← show ((([(59, 1), (557, 1), (1978659240655303067678693, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_59, prime_fiftyFiveBA_557, prime_fiftyFiveBA_1978659240655303067678693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888060 : Nat.totient 65024678625655224713124888060 = 17258724639537494549464301568 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (257, 1), (1259, 1), (3349408442130034682227, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_257, prime_fiftyFiveBA_1259, prime_fiftyFiveBA_3349408442130034682227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888061 : Nat.totient 65024678625655224713124888061 = 63684198655797153930858086400 := by
  rw [← show ((([(61, 1), (233, 1), (82478657, 1), (55469069128015321, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_61, prime_fiftyFiveBA_233, prime_fiftyFiveBA_82478657, prime_fiftyFiveBA_55469069128015321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888062 : Nat.totient 65024678625655224713124888062 = 31446426854282686608993696000 := by
  rw [← show ((([(2, 1), (31, 1), (1973, 1), (26947, 1), (2375111, 1), (8305487066761, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_31, prime_fiftyFiveBA_1973, prime_fiftyFiveBA_26947, prime_fiftyFiveBA_2375111, prime_fiftyFiveBA_8305487066761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888063 : Nat.totient 65024678625655224713124888063 = 37155916112264158284730368000 := by
  rw [← show ((([(3, 2), (7, 1), (57793, 1), (95101, 1), (3925177, 1), (47842966141, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_7, prime_fiftyFiveBA_57793, prime_fiftyFiveBA_95101, prime_fiftyFiveBA_3925177, prime_fiftyFiveBA_47842966141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888064 : Nat.totient 65024678625655224713124888064 = 32506344899662317553392353280 := by
  rw [← show ((([(2, 9), (5431, 1), (4075433, 1), (5737922695986289, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5431, prime_fiftyFiveBA_4075433, prime_fiftyFiveBA_5737922695986289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888065 : Nat.totient 65024678625655224713124888065 = 47988710863553864861330083776 := by
  rw [← show ((([(5, 1), (13, 1), (1627, 1), (614861506554349437030163, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_13, prime_fiftyFiveBA_1627, prime_fiftyFiveBA_614861506554349437030163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888066 : Nat.totient 65024678625655224713124888066 = 19602560538346756637667409920 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_11, prime_fiftyFiveBA_283, prime_fiftyFiveBA_613, prime_fiftyFiveBA_85303, prime_fiftyFiveBA_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888067 : Nat.totient 65024678625655224713124888067 = 64899871181076231959356893520 := by
  rw [← show ((([(521, 1), (124807444578992753767994027, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_521, prime_fiftyFiveBA_124807444578992753767994027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888068 : Nat.totient 65024678625655224713124888068 = 30523921205040820240213082112 := by
  rw [← show ((([(2, 2), (17, 1), (449, 1), (3929, 1), (5458489, 1), (99304400168929, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_17, prime_fiftyFiveBA_449, prime_fiftyFiveBA_3929, prime_fiftyFiveBA_5458489, prime_fiftyFiveBA_99304400168929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888069 : Nat.totient 65024678625655224713124888069 = 41465012455885119070958643776 := by
  rw [← show ((([(3, 1), (23, 1), (39324099029, 1), (23964608726411069, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_23, prime_fiftyFiveBA_39324099029, prime_fiftyFiveBA_23964608726411069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888070 : Nat.totient 65024678625655224713124888070 = 22157401445797328105576645088 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (163, 1), (5698920124947872455138027, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_7, prime_fiftyFiveBA_163, prime_fiftyFiveBA_5698920124947872455138027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888071 : Nat.totient 65024678625655224713124888071 = 65023824121854934945268516472 := by
  rw [← show ((([(76123, 1), (217917283, 1), (3919860787867319, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_76123, prime_fiftyFiveBA_217917283, prime_fiftyFiveBA_3919860787867319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888072 : Nat.totient 65024678625655224713124888072 = 21459330430665170077763834112 := by
  rw [← show ((([(2, 3), (3, 2), (127, 1), (479, 1), (14845898385209239665497, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_127, prime_fiftyFiveBA_479, prime_fiftyFiveBA_14845898385209239665497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888073 : Nat.totient 65024678625655224713124888073 = 65024678625655224713124888072 := by
  rw [← show ((([(65024678625655224713124888073, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_65024678625655224713124888073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888074 : Nat.totient 65024678625655224713124888074 = 31633625067403913227539574992 := by
  rw [← show ((([(2, 1), (37, 1), (13335683, 1), (65891778720269910347, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_37, prime_fiftyFiveBA_13335683, prime_fiftyFiveBA_65891778720269910347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888075 : Nat.totient 65024678625655224713124888075 = 34670803303105867226069637120 := by
  rw [← show ((([(3, 1), (5, 2), (4493, 1), (31159, 1), (222419, 1), (940573, 1), (29602789, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_4493, prime_fiftyFiveBA_31159, prime_fiftyFiveBA_222419, prime_fiftyFiveBA_940573, prime_fiftyFiveBA_29602789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888076 : Nat.totient 65024678625655224713124888076 = 30801163559518787947170969600 := by
  rw [← show ((([(2, 2), (19, 1), (28022106501281, 1), (30532603843121, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_19, prime_fiftyFiveBA_28022106501281, prime_fiftyFiveBA_30532603843121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888077 : Nat.totient 65024678625655224713124888077 = 50219262904128788651747328000 := by
  rw [← show ((([(7, 1), (11, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_7, prime_fiftyFiveBA_11, prime_fiftyFiveBA_113, prime_fiftyFiveBA_54421, prime_fiftyFiveBA_97654321, prime_fiftyFiveBA_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888078 : Nat.totient 65024678625655224713124888078 = 20007561668039489372297040000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (630151, 1), (5405121677, 1), (18827391551, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_13, prime_fiftyFiveBA_630151, prime_fiftyFiveBA_5405121677, prime_fiftyFiveBA_18827391551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888079 : Nat.totient 65024678625655224713124888079 = 65024662344049629958909950000 := by
  rw [← show ((([(3993751, 1), (16281605594754210944329, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3993751, prime_fiftyFiveBA_16281605594754210944329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888080 : Nat.totient 65024678625655224713124888080 = 25480108256709295607880337920 := by
  rw [← show ((([(2, 4), (5, 1), (67, 1), (181, 1), (67024695540586320517363, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_67, prime_fiftyFiveBA_181, prime_fiftyFiveBA_67024695540586320517363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888081 : Nat.totient 65024678625655224713124888081 = 43349785750436816475416592036 := by
  rw [← show ((([(3, 3), (2408321430579823137523144003, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_2408321430579823137523144003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888082 : Nat.totient 65024678625655224713124888082 = 31494417903852099417849600000 := by
  rw [← show ((([(2, 1), (41, 1), (151, 1), (2129, 1), (417019, 1), (5915015824042901, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_41, prime_fiftyFiveBA_151, prime_fiftyFiveBA_2129, prime_fiftyFiveBA_417019, prime_fiftyFiveBA_5915015824042901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888083 : Nat.totient 65024678625655224713124888083 = 65024656552960894714705578600 := by
  rw [← show ((([(2945933, 1), (22072694329998416363551, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2945933, prime_fiftyFiveBA_22072694329998416363551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888084 : Nat.totient 65024678625655224713124888084 = 18467229654591878145389478912 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (167, 1), (11748679, 1), (394542161159196257, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_7, prime_fiftyFiveBA_167, prime_fiftyFiveBA_11748679, prime_fiftyFiveBA_394542161159196257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888085 : Nat.totient 65024678625655224713124888085 = 48959757968995169591568657408 := by
  rw [← show ((([(5, 1), (17, 1), (889731133, 1), (859806059102301397, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_17, prime_fiftyFiveBA_889731133, prime_fiftyFiveBA_859806059102301397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888086 : Nat.totient 65024678625655224713124888086 = 31756238059462316865297247968 := by
  rw [← show ((([(2, 1), (43, 1), (93644869, 1), (8074130727352557229, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_43, prime_fiftyFiveBA_93644869, prime_fiftyFiveBA_8074130727352557229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888087 : Nat.totient 65024678625655224713124888087 = 41854965552145891769367744000 := by
  rw [← show ((([(3, 1), (29, 1), (747410099145462353024424001, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_29, prime_fiftyFiveBA_747410099145462353024424001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888088 : Nat.totient 65024678625655224713124888088 = 29200546977159685770729856000 := by
  rw [← show ((([(2, 3), (11, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_11, prime_fiftyFiveBA_83, prime_fiftyFiveBA_1433741, prime_fiftyFiveBA_106163831, prime_fiftyFiveBA_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888089 : Nat.totient 65024678625655224713124888089 = 65024674829078558972633665200 := by
  rw [← show ((([(17198551, 1), (4146381443, 1), (911836775173, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_17198551, prime_fiftyFiveBA_4146381443, prime_fiftyFiveBA_911836775173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888090 : Nat.totient 65024678625655224713124888090 = 17339657083528612530139747200 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (67901, 1), (9392503, 1), (1132865085569267, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5, prime_fiftyFiveBA_67901, prime_fiftyFiveBA_9392503, prime_fiftyFiveBA_1132865085569267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888091 : Nat.totient 65024678625655224713124888091 = 51423243484113816788568775680 := by
  rw [← show ((([(7, 1), (13, 1), (2131, 1), (92639, 1), (426779, 1), (2567447, 1), (3303353, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_7, prime_fiftyFiveBA_13, prime_fiftyFiveBA_2131, prime_fiftyFiveBA_92639, prime_fiftyFiveBA_426779, prime_fiftyFiveBA_2567447, prime_fiftyFiveBA_3303353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888092 : Nat.totient 65024678625655224713124888092 = 30850795916531794619617766400 := by
  rw [← show ((([(2, 2), (23, 1), (139, 1), (1361, 1), (19963, 1), (100696031, 1), (1858571623, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_23, prime_fiftyFiveBA_139, prime_fiftyFiveBA_1361, prime_fiftyFiveBA_19963, prime_fiftyFiveBA_100696031, prime_fiftyFiveBA_1858571623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888093 : Nat.totient 65024678625655224713124888093 = 41951034369405749555675377920 := by
  rw [← show ((([(3, 1), (31, 1), (113017, 1), (6186592218418299113353, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_31, prime_fiftyFiveBA_113017, prime_fiftyFiveBA_6186592218418299113353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888094 : Nat.totient 65024678625655224713124888094 = 31814823853792291899574202880 := by
  rw [← show ((([(2, 1), (47, 1), (5521, 1), (8567186909, 1), (14624949386309, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_47, prime_fiftyFiveBA_5521, prime_fiftyFiveBA_8567186909, prime_fiftyFiveBA_14624949386309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888095 : Nat.totient 65024678625655224713124888095 = 49000808878683173856313344000 := by
  rw [← show ((([(5, 1), (19, 1), (241, 1), (641, 1), (4430773372276762682321, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5, prime_fiftyFiveBA_19, prime_fiftyFiveBA_241, prime_fiftyFiveBA_641, prime_fiftyFiveBA_4430773372276762682321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888096 : Nat.totient 65024678625655224713124888096 = 21670835356346109716433438720 := by
  rw [← show ((([(2, 5), (3, 1), (5689, 1), (87541, 1), (1360064623232344999, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_3, prime_fiftyFiveBA_5689, prime_fiftyFiveBA_87541, prime_fiftyFiveBA_1360064623232344999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888097 : Nat.totient 65024678625655224713124888097 = 65009530402340681515552140000 := by
  rw [← show ((([(5087, 1), (27481, 1), (465140274343451881751, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_5087, prime_fiftyFiveBA_27481, prime_fiftyFiveBA_465140274343451881751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888098 : Nat.totient 65024678625655224713124888098 = 27867719410989579526862205000 := by
  rw [← show ((([(2, 1), (7, 2), (5262266536651, 1), (126089608766851, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_7, prime_fiftyFiveBA_5262266536651, prime_fiftyFiveBA_126089608766851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888099 : Nat.totient 65024678625655224713124888099 = 39338548637886845185997882880 := by
  rw [← show ((([(3, 2), (11, 1), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_3, prime_fiftyFiveBA_11, prime_fiftyFiveBA_569, prime_fiftyFiveBA_37039, prime_fiftyFiveBA_1544987, prime_fiftyFiveBA_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFiveBA_65024678625655224713124888100 : Nat.totient 65024678625655224713124888100 = 25913157505263343395383116800 := by
  rw [← show ((([(2, 2), (5, 2), (269, 1), (1127981, 1), (2143009765547021929, 1)] : List FactorBlock).map factorBlockValue).prod) = 65024678625655224713124888100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFiveBA_2, prime_fiftyFiveBA_5, prime_fiftyFiveBA_269, prime_fiftyFiveBA_1127981, prime_fiftyFiveBA_2143009765547021929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyFiveBA : certifiedKill 1 65024678625655224713124887999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyFiveBA_65024678625655224713124888000, phi_fiftyFiveBA_65024678625655224713124888001, phi_fiftyFiveBA_65024678625655224713124888002,
    phi_fiftyFiveBA_65024678625655224713124888003, phi_fiftyFiveBA_65024678625655224713124888004, phi_fiftyFiveBA_65024678625655224713124888005,
    phi_fiftyFiveBA_65024678625655224713124888006, phi_fiftyFiveBA_65024678625655224713124888007, phi_fiftyFiveBA_65024678625655224713124888008,
    phi_fiftyFiveBA_65024678625655224713124888009, phi_fiftyFiveBA_65024678625655224713124888010, phi_fiftyFiveBA_65024678625655224713124888011,
    phi_fiftyFiveBA_65024678625655224713124888012, phi_fiftyFiveBA_65024678625655224713124888013, phi_fiftyFiveBA_65024678625655224713124888014,
    phi_fiftyFiveBA_65024678625655224713124888015, phi_fiftyFiveBA_65024678625655224713124888016, phi_fiftyFiveBA_65024678625655224713124888017,
    phi_fiftyFiveBA_65024678625655224713124888018, phi_fiftyFiveBA_65024678625655224713124888019, phi_fiftyFiveBA_65024678625655224713124888020,
    phi_fiftyFiveBA_65024678625655224713124888021, phi_fiftyFiveBA_65024678625655224713124888022, phi_fiftyFiveBA_65024678625655224713124888023,
    phi_fiftyFiveBA_65024678625655224713124888024, phi_fiftyFiveBA_65024678625655224713124888025, phi_fiftyFiveBA_65024678625655224713124888026,
    phi_fiftyFiveBA_65024678625655224713124888027, phi_fiftyFiveBA_65024678625655224713124888028, phi_fiftyFiveBA_65024678625655224713124888029,
    phi_fiftyFiveBA_65024678625655224713124888030, phi_fiftyFiveBA_65024678625655224713124888031, phi_fiftyFiveBA_65024678625655224713124888032,
    phi_fiftyFiveBA_65024678625655224713124888033, phi_fiftyFiveBA_65024678625655224713124888034, phi_fiftyFiveBA_65024678625655224713124888035,
    phi_fiftyFiveBA_65024678625655224713124888036, phi_fiftyFiveBA_65024678625655224713124888037, phi_fiftyFiveBA_65024678625655224713124888038,
    phi_fiftyFiveBA_65024678625655224713124888039, phi_fiftyFiveBA_65024678625655224713124888040, phi_fiftyFiveBA_65024678625655224713124888041,
    phi_fiftyFiveBA_65024678625655224713124888042, phi_fiftyFiveBA_65024678625655224713124888043, phi_fiftyFiveBA_65024678625655224713124888044,
    phi_fiftyFiveBA_65024678625655224713124888045, phi_fiftyFiveBA_65024678625655224713124888046, phi_fiftyFiveBA_65024678625655224713124888047,
    phi_fiftyFiveBA_65024678625655224713124888048, phi_fiftyFiveBA_65024678625655224713124888049, phi_fiftyFiveBA_65024678625655224713124888050,
    phi_fiftyFiveBA_65024678625655224713124888051, phi_fiftyFiveBA_65024678625655224713124888052, phi_fiftyFiveBA_65024678625655224713124888053,
    phi_fiftyFiveBA_65024678625655224713124888054, phi_fiftyFiveBA_65024678625655224713124888055, phi_fiftyFiveBA_65024678625655224713124888056,
    phi_fiftyFiveBA_65024678625655224713124888057, phi_fiftyFiveBA_65024678625655224713124888058, phi_fiftyFiveBA_65024678625655224713124888059,
    phi_fiftyFiveBA_65024678625655224713124888060, phi_fiftyFiveBA_65024678625655224713124888061, phi_fiftyFiveBA_65024678625655224713124888062,
    phi_fiftyFiveBA_65024678625655224713124888063, phi_fiftyFiveBA_65024678625655224713124888064, phi_fiftyFiveBA_65024678625655224713124888065,
    phi_fiftyFiveBA_65024678625655224713124888066, phi_fiftyFiveBA_65024678625655224713124888067, phi_fiftyFiveBA_65024678625655224713124888068,
    phi_fiftyFiveBA_65024678625655224713124888069, phi_fiftyFiveBA_65024678625655224713124888070, phi_fiftyFiveBA_65024678625655224713124888071,
    phi_fiftyFiveBA_65024678625655224713124888072, phi_fiftyFiveBA_65024678625655224713124888073, phi_fiftyFiveBA_65024678625655224713124888074,
    phi_fiftyFiveBA_65024678625655224713124888075, phi_fiftyFiveBA_65024678625655224713124888076, phi_fiftyFiveBA_65024678625655224713124888077,
    phi_fiftyFiveBA_65024678625655224713124888078, phi_fiftyFiveBA_65024678625655224713124888079, phi_fiftyFiveBA_65024678625655224713124888080,
    phi_fiftyFiveBA_65024678625655224713124888081, phi_fiftyFiveBA_65024678625655224713124888082, phi_fiftyFiveBA_65024678625655224713124888083,
    phi_fiftyFiveBA_65024678625655224713124888084, phi_fiftyFiveBA_65024678625655224713124888085, phi_fiftyFiveBA_65024678625655224713124888086,
    phi_fiftyFiveBA_65024678625655224713124888087, phi_fiftyFiveBA_65024678625655224713124888088, phi_fiftyFiveBA_65024678625655224713124888089,
    phi_fiftyFiveBA_65024678625655224713124888090, phi_fiftyFiveBA_65024678625655224713124888091, phi_fiftyFiveBA_65024678625655224713124888092,
    phi_fiftyFiveBA_65024678625655224713124888093, phi_fiftyFiveBA_65024678625655224713124888094, phi_fiftyFiveBA_65024678625655224713124888095,
    phi_fiftyFiveBA_65024678625655224713124888096, phi_fiftyFiveBA_65024678625655224713124888097, phi_fiftyFiveBA_65024678625655224713124888098,
    phi_fiftyFiveBA_65024678625655224713124888099, phi_fiftyFiveBA_65024678625655224713124888100]

end TotientTailPeriodKiller
end Erdos249257
