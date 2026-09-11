import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def quadFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem quadFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    quadFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [quadFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [quadFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then quadFastPow a n * quadFastPow a n * a
        else quadFastPow a n * quadFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_quadB_2 : Nat.Prime 2 := by norm_num
private theorem prime_quadB_3 : Nat.Prime 3 := by norm_num
private theorem prime_quadB_5 : Nat.Prime 5 := by norm_num
private theorem prime_quadB_7 : Nat.Prime 7 := by norm_num
private theorem prime_quadB_11 : Nat.Prime 11 := by norm_num
private theorem prime_quadB_13 : Nat.Prime 13 := by norm_num
private theorem prime_quadB_17 : Nat.Prime 17 := by norm_num
private theorem prime_quadB_19 : Nat.Prime 19 := by norm_num
private theorem prime_quadB_23 : Nat.Prime 23 := by norm_num
private theorem prime_quadB_29 : Nat.Prime 29 := by norm_num
private theorem prime_quadB_31 : Nat.Prime 31 := by norm_num
private theorem prime_quadB_37 : Nat.Prime 37 := by norm_num
private theorem prime_quadB_41 : Nat.Prime 41 := by norm_num
private theorem prime_quadB_43 : Nat.Prime 43 := by norm_num
private theorem prime_quadB_47 : Nat.Prime 47 := by norm_num
private theorem prime_quadB_53 : Nat.Prime 53 := by norm_num
private theorem prime_quadB_59 : Nat.Prime 59 := by norm_num
private theorem prime_quadB_61 : Nat.Prime 61 := by norm_num
private theorem prime_quadB_67 : Nat.Prime 67 := by norm_num
private theorem prime_quadB_71 : Nat.Prime 71 := by norm_num
private theorem prime_quadB_73 : Nat.Prime 73 := by norm_num
private theorem prime_quadB_79 : Nat.Prime 79 := by norm_num
private theorem prime_quadB_83 : Nat.Prime 83 := by norm_num
private theorem prime_quadB_89 : Nat.Prime 89 := by norm_num
private theorem prime_quadB_97 : Nat.Prime 97 := by norm_num
private theorem prime_quadB_101 : Nat.Prime 101 := by norm_num
private theorem prime_quadB_103 : Nat.Prime 103 := by norm_num
private theorem prime_quadB_107 : Nat.Prime 107 := by norm_num
private theorem prime_quadB_109 : Nat.Prime 109 := by norm_num
private theorem prime_quadB_113 : Nat.Prime 113 := by norm_num
private theorem prime_quadB_127 : Nat.Prime 127 := by norm_num
private theorem prime_quadB_131 : Nat.Prime 131 := by norm_num
private theorem prime_quadB_137 : Nat.Prime 137 := by norm_num
private theorem prime_quadB_139 : Nat.Prime 139 := by norm_num
private theorem prime_quadB_149 : Nat.Prime 149 := by norm_num
private theorem prime_quadB_151 : Nat.Prime 151 := by norm_num
private theorem prime_quadB_157 : Nat.Prime 157 := by norm_num
private theorem prime_quadB_167 : Nat.Prime 167 := by norm_num
private theorem prime_quadB_173 : Nat.Prime 173 := by norm_num
private theorem prime_quadB_179 : Nat.Prime 179 := by norm_num
private theorem prime_quadB_191 : Nat.Prime 191 := by norm_num
private theorem prime_quadB_197 : Nat.Prime 197 := by norm_num
private theorem prime_quadB_211 : Nat.Prime 211 := by norm_num
private theorem prime_quadB_223 : Nat.Prime 223 := by norm_num
private theorem prime_quadB_229 : Nat.Prime 229 := by norm_num
private theorem prime_quadB_233 : Nat.Prime 233 := by norm_num
private theorem prime_quadB_239 : Nat.Prime 239 := by norm_num
private theorem prime_quadB_241 : Nat.Prime 241 := by norm_num
private theorem prime_quadB_251 : Nat.Prime 251 := by norm_num
private theorem prime_quadB_257 : Nat.Prime 257 := by norm_num
private theorem prime_quadB_263 : Nat.Prime 263 := by norm_num
private theorem prime_quadB_271 : Nat.Prime 271 := by norm_num
private theorem prime_quadB_277 : Nat.Prime 277 := by norm_num
private theorem prime_quadB_293 : Nat.Prime 293 := by norm_num
private theorem prime_quadB_307 : Nat.Prime 307 := by norm_num
private theorem prime_quadB_311 : Nat.Prime 311 := by norm_num
private theorem prime_quadB_313 : Nat.Prime 313 := by norm_num
private theorem prime_quadB_317 : Nat.Prime 317 := by norm_num
private theorem prime_quadB_331 : Nat.Prime 331 := by norm_num
private theorem prime_quadB_337 : Nat.Prime 337 := by norm_num
private theorem prime_quadB_347 : Nat.Prime 347 := by norm_num
private theorem prime_quadB_349 : Nat.Prime 349 := by norm_num
private theorem prime_quadB_373 : Nat.Prime 373 := by norm_num
private theorem prime_quadB_379 : Nat.Prime 379 := by norm_num
private theorem prime_quadB_383 : Nat.Prime 383 := by norm_num
private theorem prime_quadB_389 : Nat.Prime 389 := by norm_num
private theorem prime_quadB_397 : Nat.Prime 397 := by norm_num
private theorem prime_quadB_401 : Nat.Prime 401 := by norm_num
private theorem prime_quadB_409 : Nat.Prime 409 := by norm_num
private theorem prime_quadB_419 : Nat.Prime 419 := by norm_num
private theorem prime_quadB_421 : Nat.Prime 421 := by norm_num
private theorem prime_quadB_431 : Nat.Prime 431 := by norm_num
private theorem prime_quadB_433 : Nat.Prime 433 := by norm_num
private theorem prime_quadB_439 : Nat.Prime 439 := by norm_num
private theorem prime_quadB_443 : Nat.Prime 443 := by norm_num
private theorem prime_quadB_457 : Nat.Prime 457 := by norm_num
private theorem prime_quadB_461 : Nat.Prime 461 := by norm_num
private theorem prime_quadB_463 : Nat.Prime 463 := by norm_num
private theorem prime_quadB_467 : Nat.Prime 467 := by norm_num
private theorem prime_quadB_479 : Nat.Prime 479 := by norm_num
private theorem prime_quadB_491 : Nat.Prime 491 := by norm_num
private theorem prime_quadB_541 : Nat.Prime 541 := by norm_num
private theorem prime_quadB_563 : Nat.Prime 563 := by norm_num
private theorem prime_quadB_569 : Nat.Prime 569 := by norm_num
private theorem prime_quadB_571 : Nat.Prime 571 := by norm_num
private theorem prime_quadB_587 : Nat.Prime 587 := by norm_num
private theorem prime_quadB_593 : Nat.Prime 593 := by norm_num
private theorem prime_quadB_599 : Nat.Prime 599 := by norm_num
private theorem prime_quadB_601 : Nat.Prime 601 := by norm_num
private theorem prime_quadB_653 : Nat.Prime 653 := by norm_num
private theorem prime_quadB_659 : Nat.Prime 659 := by norm_num
private theorem prime_quadB_673 : Nat.Prime 673 := by norm_num
private theorem prime_quadB_677 : Nat.Prime 677 := by norm_num
private theorem prime_quadB_691 : Nat.Prime 691 := by norm_num
private theorem prime_quadB_709 : Nat.Prime 709 := by norm_num
private theorem prime_quadB_727 : Nat.Prime 727 := by norm_num
private theorem prime_quadB_733 : Nat.Prime 733 := by norm_num
private theorem prime_quadB_739 : Nat.Prime 739 := by norm_num
private theorem prime_quadB_751 : Nat.Prime 751 := by norm_num
private theorem prime_quadB_757 : Nat.Prime 757 := by norm_num
private theorem prime_quadB_787 : Nat.Prime 787 := by norm_num
private theorem prime_quadB_797 : Nat.Prime 797 := by norm_num
private theorem prime_quadB_811 : Nat.Prime 811 := by norm_num
private theorem prime_quadB_821 : Nat.Prime 821 := by norm_num
private theorem prime_quadB_823 : Nat.Prime 823 := by norm_num
private theorem prime_quadB_853 : Nat.Prime 853 := by norm_num
private theorem prime_quadB_859 : Nat.Prime 859 := by norm_num
private theorem prime_quadB_863 : Nat.Prime 863 := by norm_num
private theorem prime_quadB_947 : Nat.Prime 947 := by norm_num
private theorem prime_quadB_967 : Nat.Prime 967 := by norm_num
private theorem prime_quadB_983 : Nat.Prime 983 := by norm_num
private theorem prime_quadB_991 : Nat.Prime 991 := by norm_num
private theorem prime_quadB_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_quadB_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_quadB_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_quadB_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_quadB_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_quadB_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_quadB_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_quadB_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_quadB_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_quadB_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_quadB_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_quadB_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_quadB_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_quadB_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_quadB_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_quadB_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_quadB_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_quadB_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_quadB_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_quadB_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_quadB_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_quadB_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_quadB_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_quadB_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_quadB_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_quadB_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_quadB_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_quadB_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_quadB_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_quadB_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_quadB_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_quadB_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_quadB_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_quadB_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_quadB_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_quadB_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_quadB_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_quadB_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_quadB_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_quadB_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_quadB_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_quadB_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_quadB_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_quadB_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_quadB_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_quadB_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_quadB_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_quadB_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_quadB_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_quadB_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_quadB_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_quadB_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_quadB_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_quadB_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_quadB_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_quadB_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_quadB_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_quadB_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_quadB_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_quadB_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_quadB_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_quadB_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_quadB_4201 : Nat.Prime 4201 := by norm_num
private theorem prime_quadB_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_quadB_4337 : Nat.Prime 4337 := by norm_num
private theorem prime_quadB_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_quadB_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_quadB_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_quadB_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_quadB_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_quadB_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_quadB_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_quadB_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_quadB_5519 : Nat.Prime 5519 := by norm_num
private theorem prime_quadB_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_quadB_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_quadB_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_quadB_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_quadB_6299 : Nat.Prime 6299 := by norm_num
private theorem prime_quadB_6329 : Nat.Prime 6329 := by norm_num
private theorem prime_quadB_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_quadB_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_quadB_6997 : Nat.Prime 6997 := by norm_num
private theorem prime_quadB_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_quadB_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_quadB_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_quadB_8461 : Nat.Prime 8461 := by norm_num
private theorem prime_quadB_8761 : Nat.Prime 8761 := by norm_num
private theorem prime_quadB_9043 : Nat.Prime 9043 := by norm_num
private theorem prime_quadB_9209 : Nat.Prime 9209 := by norm_num
private theorem prime_quadB_9221 : Nat.Prime 9221 := by norm_num
private theorem prime_quadB_9343 : Nat.Prime 9343 := by norm_num
private theorem prime_quadB_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_quadB_10337 : Nat.Prime 10337 := by norm_num
private theorem prime_quadB_10867 : Nat.Prime 10867 := by norm_num
private theorem prime_quadB_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_quadB_11503 : Nat.Prime 11503 := by norm_num
private theorem prime_quadB_11923 : Nat.Prime 11923 := by norm_num
private theorem prime_quadB_11927 : Nat.Prime 11927 := by norm_num
private theorem prime_quadB_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_quadB_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_quadB_12611 : Nat.Prime 12611 := by norm_num
private theorem prime_quadB_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_quadB_13183 : Nat.Prime 13183 := by norm_num
private theorem prime_quadB_13567 : Nat.Prime 13567 := by norm_num
private theorem prime_quadB_13709 : Nat.Prime 13709 := by norm_num
private theorem prime_quadB_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_quadB_14537 : Nat.Prime 14537 := by norm_num
private theorem prime_quadB_15427 : Nat.Prime 15427 := by norm_num
private theorem prime_quadB_16823 : Nat.Prime 16823 := by norm_num
private theorem prime_quadB_18713 : Nat.Prime 18713 := by norm_num
private theorem prime_quadB_18757 : Nat.Prime 18757 := by norm_num
private theorem prime_quadB_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_quadB_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_quadB_19447 : Nat.Prime 19447 := by norm_num
private theorem prime_quadB_21587 : Nat.Prime 21587 := by norm_num
private theorem prime_quadB_22343 : Nat.Prime 22343 := by norm_num
private theorem prime_quadB_22397 : Nat.Prime 22397 := by norm_num
private theorem prime_quadB_22807 : Nat.Prime 22807 := by norm_num
private theorem prime_quadB_23017 : Nat.Prime 23017 := by norm_num
private theorem prime_quadB_27739 : Nat.Prime 27739 := by norm_num
private theorem prime_quadB_27743 : Nat.Prime 27743 := by norm_num
private theorem prime_quadB_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_quadB_29021 : Nat.Prime 29021 := by norm_num
private theorem prime_quadB_29717 : Nat.Prime 29717 := by norm_num
private theorem prime_quadB_30427 : Nat.Prime 30427 := by norm_num
private theorem prime_quadB_31723 : Nat.Prime 31723 := by norm_num
private theorem prime_quadB_33347 : Nat.Prime 33347 := by norm_num
private theorem prime_quadB_34159 : Nat.Prime 34159 := by norm_num
private theorem prime_quadB_34273 : Nat.Prime 34273 := by norm_num
private theorem prime_quadB_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_quadB_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_quadB_35863 : Nat.Prime 35863 := by norm_num
private theorem prime_quadB_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_quadB_37397 : Nat.Prime 37397 := by norm_num
private theorem prime_quadB_37463 : Nat.Prime 37463 := by norm_num
private theorem prime_quadB_37547 : Nat.Prime 37547 := by norm_num
private theorem prime_quadB_38329 : Nat.Prime 38329 := by norm_num
private theorem prime_quadB_39551 : Nat.Prime 39551 := by norm_num
private theorem prime_quadB_40577 : Nat.Prime 40577 := by norm_num
private theorem prime_quadB_40739 : Nat.Prime 40739 := by norm_num
private theorem prime_quadB_41729 : Nat.Prime 41729 := by norm_num
private theorem prime_quadB_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_quadB_49627 : Nat.Prime 49627 := by norm_num
private theorem prime_quadB_50227 : Nat.Prime 50227 := by norm_num
private theorem prime_quadB_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_quadB_55843 : Nat.Prime 55843 := by norm_num
private theorem prime_quadB_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_quadB_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_quadB_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_quadB_72689 : Nat.Prime 72689 := by norm_num
private theorem prime_quadB_73771 : Nat.Prime 73771 := by norm_num
private theorem prime_quadB_76367 : Nat.Prime 76367 := by norm_num
private theorem prime_quadB_79811 : Nat.Prime 79811 := by norm_num
private theorem prime_quadB_80021 : Nat.Prime 80021 := by norm_num
private theorem prime_quadB_80819 : Nat.Prime 80819 := by norm_num
private theorem prime_quadB_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_quadB_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_quadB_105683 : Nat.Prime 105683 := by norm_num
private theorem prime_quadB_108461 : Nat.Prime 108461 := by norm_num
private theorem prime_quadB_108463 : Nat.Prime 108463 := by norm_num
private theorem prime_quadB_109469 : Nat.Prime 109469 := by norm_num
private theorem prime_quadB_111767 : Nat.Prime 111767 := by norm_num
private theorem prime_quadB_115901 : Nat.Prime 115901 := by norm_num
private theorem prime_quadB_132233 : Nat.Prime 132233 := by norm_num
private theorem prime_quadB_133559 : Nat.Prime 133559 := by norm_num
private theorem prime_quadB_139967 : Nat.Prime 139967 := by norm_num
private theorem prime_quadB_140197 : Nat.Prime 140197 := by norm_num
private theorem prime_quadB_141551 : Nat.Prime 141551 := by norm_num
private theorem prime_quadB_149689 : Nat.Prime 149689 := by norm_num
private theorem prime_quadB_152287 : Nat.Prime 152287 := by norm_num
private theorem prime_quadB_156139 : Nat.Prime 156139 := by norm_num
private theorem prime_quadB_158077 : Nat.Prime 158077 := by norm_num
private theorem prime_quadB_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_quadB_177409 : Nat.Prime 177409 := by norm_num
private theorem prime_quadB_183707 : Nat.Prime 183707 := by norm_num
private theorem prime_quadB_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_quadB_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_quadB_222107 : Nat.Prime 222107 := by norm_num
private theorem prime_quadB_228337 : Nat.Prime 228337 := by norm_num
private theorem prime_quadB_228581 : Nat.Prime 228581 := by norm_num
private theorem prime_quadB_241513 : Nat.Prime 241513 := by norm_num
private theorem prime_quadB_248821 : Nat.Prime 248821 := by norm_num
private theorem prime_quadB_279991 : Nat.Prime 279991 := by norm_num
private theorem prime_quadB_283163 : Nat.Prime 283163 := by norm_num
private theorem prime_quadB_300239 : Nat.Prime 300239 := by norm_num
private theorem prime_quadB_303007 : Nat.Prime 303007 := by norm_num
private theorem prime_quadB_310627 : Nat.Prime 310627 := by norm_num
private theorem prime_quadB_344213 : Nat.Prime 344213 := by norm_num
private theorem prime_quadB_372709 : Nat.Prime 372709 := by norm_num
private theorem prime_quadB_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_quadB_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_quadB_397763 : Nat.Prime 397763 := by norm_num
private theorem prime_quadB_443941 : Nat.Prime 443941 := by norm_num
private theorem prime_quadB_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_quadB_575747 : Nat.Prime 575747 := by norm_num
private theorem prime_quadB_623279 : Nat.Prime 623279 := by norm_num
private theorem prime_quadB_629897 : Nat.Prime 629897 := by norm_num
private theorem prime_quadB_671903 : Nat.Prime 671903 := by norm_num
private theorem prime_quadB_678901 : Nat.Prime 678901 := by norm_num
private theorem prime_quadB_685369 : Nat.Prime 685369 := by norm_num
private theorem prime_quadB_829627 : Nat.Prime 829627 := by norm_num
private theorem prime_quadB_865483 : Nat.Prime 865483 := by norm_num
private theorem prime_quadB_878131 : Nat.Prime 878131 := by norm_num
private theorem prime_quadB_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_quadB_911749 : Nat.Prime 911749 := by norm_num
private theorem prime_quadB_940369 : Nat.Prime 940369 := by norm_num
private theorem prime_quadB_1107569 : Nat.Prime 1107569 := by norm_num
private theorem prime_quadB_1115447 : Nat.Prime 1115447 := by norm_num
private theorem prime_quadB_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_quadB_1257229 : Nat.Prime 1257229 := by norm_num
private theorem prime_quadB_1271359 : Nat.Prime 1271359 := by norm_num
private theorem prime_quadB_1319293 : Nat.Prime 1319293 := by norm_num
private theorem prime_quadB_1350341 : Nat.Prime 1350341 := by norm_num
private theorem prime_quadB_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_quadB_1701179 : Nat.Prime 1701179 := by norm_num
private theorem prime_quadB_1789993 : Nat.Prime 1789993 := by norm_num
private theorem prime_quadB_1800709 : Nat.Prime 1800709 := by norm_num
private theorem prime_quadB_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_quadB_2017987 : Nat.Prime 2017987 := by norm_num
private theorem prime_quadB_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_quadB_2075831 : Nat.Prime 2075831 := by norm_num
private theorem prime_quadB_2178733 : Nat.Prime 2178733 := by norm_num
private theorem prime_quadB_2544331 : Nat.Prime 2544331 := by norm_num
private theorem prime_quadB_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_quadB_2685877 : Nat.Prime 2685877 := by norm_num
private theorem prime_quadB_3322747 : Nat.Prime 3322747 := by norm_num
private theorem prime_quadB_3351109 : Nat.Prime 3351109 := by norm_num
private theorem prime_quadB_3477841 : Nat.Prime 3477841 := by norm_num
private theorem prime_quadB_3592597 : Nat.Prime 3592597 := by norm_num
private theorem prime_quadB_3623449 : Nat.Prime 3623449 := by norm_num
private theorem prime_quadB_4384091 : Nat.Prime 4384091 := by norm_num
private theorem prime_quadB_4597709 : Nat.Prime 4597709 := by norm_num
private theorem prime_quadB_4824031 : Nat.Prime 4824031 := by norm_num
private theorem prime_quadB_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_quadB_5054317 : Nat.Prime 5054317 := by norm_num
private theorem prime_quadB_5250043 : Nat.Prime 5250043 := by norm_num
private theorem prime_quadB_5315977 : Nat.Prime 5315977 := by norm_num
private theorem prime_quadB_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_quadB_6514591 : Nat.Prime 6514591 := by norm_num
private theorem prime_quadB_6888173 : Nat.Prime 6888173 := by norm_num
private theorem prime_quadB_6947861 : Nat.Prime 6947861 := by norm_num
private theorem prime_quadB_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_quadB_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_quadB_7846799 : Nat.Prime 7846799 := by norm_num
private theorem prime_quadB_7906729 : Nat.Prime 7906729 := by norm_num
private theorem prime_quadB_7955917 : Nat.Prime 7955917 := by norm_num
private theorem prime_quadB_7982567 : Nat.Prime 7982567 := by norm_num
private theorem prime_quadB_8295863 : Nat.Prime 8295863 := by norm_num
private theorem prime_quadB_9427753 : Nat.Prime 9427753 := by norm_num
private theorem prime_quadB_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_quadB_10653997 : Nat.Prime 10653997 := by norm_num
private theorem prime_quadB_10909949 : Nat.Prime 10909949 := by norm_num
private theorem prime_quadB_11250929 : Nat.Prime 11250929 := by norm_num
private theorem prime_quadB_11537291 : Nat.Prime 11537291 := by norm_num
private theorem prime_quadB_11746253 : Nat.Prime 11746253 := by norm_num
private theorem prime_quadB_12154501 : Nat.Prime 12154501 := by norm_num
private theorem prime_quadB_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_quadB_14839757 : Nat.Prime 14839757 := by norm_num
private theorem prime_quadB_15535361 : Nat.Prime 15535361 := by norm_num
private theorem prime_quadB_15587213 : Nat.Prime 15587213 := by norm_num
private theorem prime_quadB_16236019 : Nat.Prime 16236019 := by norm_num
private theorem prime_quadB_18044017 : Nat.Prime 18044017 := by norm_num
private theorem prime_quadB_18731981 : Nat.Prime 18731981 := by norm_num

private theorem prime_quadB_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_23
      · exact prime_quadB_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_21263909 : Nat.Prime 21263909 := by
  apply lucas_primality 21263909 (2 : ZMod 21263909)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5315977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5315977, 1)] : List FactorBlock).map factorBlockValue).prod = 21263909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5315977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21263909) ^ 10631954 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 21263909) ^ 4 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_23413451 : Nat.Prime 23413451 := by
  apply lucas_primality 23413451 (2 : ZMod 23413451)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (197, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (197, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod = 23413451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_197
      · exact prime_quadB_2377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23413451) ^ 11706725 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 23413451) ^ 4682690 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 23413451) ^ 118850 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 23413451) ^ 9850 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_23492507 : Nat.Prime 23492507 := by
  apply lucas_primality 23492507 (2 : ZMod 23492507)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11746253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11746253, 1)] : List FactorBlock).map factorBlockValue).prod = 23492507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11746253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 23492507) ^ 11746253 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 23492507) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_37463963 : Nat.Prime 37463963 := by
  apply lucas_primality 37463963 (2 : ZMod 37463963)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18731981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18731981, 1)] : List FactorBlock).map factorBlockValue).prod = 37463963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_18731981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37463963) ^ 18731981 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 37463963) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_40376737 : Nat.Prime 40376737 := by
  apply lucas_primality 40376737 (10 : ZMod 40376737)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (140197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (140197, 1)] : List FactorBlock).map factorBlockValue).prod = 40376737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_140197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 40376737) ^ 20188368 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 40376737) ^ 13458912 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 40376737) ^ 288 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_49777621 : Nat.Prime 49777621 := by
  apply lucas_primality 49777621 (6 : ZMod 49777621)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (829627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (829627, 1)] : List FactorBlock).map factorBlockValue).prod = 49777621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_829627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 49777621) ^ 24888810 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 49777621) ^ 16592540 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 49777621) ^ 9955524 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 49777621) ^ 60 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_108608761 : Nat.Prime 108608761 := by
  apply lucas_primality 108608761 (34 : ZMod 108608761)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 1), (13, 1), (23, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 1), (13, 1), (23, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod = 108608761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_23
      · exact prime_quadB_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 108608761) ^ 54304380 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 36202920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 21721752 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 8354520 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 4722120 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (34 : ZMod 108608761) ^ 107640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_116384069 : Nat.Prime 116384069 := by
  apply lucas_primality 116384069 (2 : ZMod 116384069)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod = 116384069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_131
      · exact prime_quadB_222107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116384069) ^ 58192034 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 116384069) ^ 888428 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 116384069) ^ 524 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_162618881 : Nat.Prime 162618881 := by
  apply lucas_primality 162618881 (15 : ZMod 162618881)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (5, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (5, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod = 162618881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_139
      · exact prime_quadB_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 162618881) ^ 81309440 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 32523776 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 1169920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (15 : ZMod 162618881) ^ 355840 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_191
      · exact prime_quadB_383
      · exact prime_quadB_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_269456833 : Nat.Prime 269456833 := by
  apply lucas_primality 269456833 (5 : ZMod 269456833)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (677, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (677, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod = 269456833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_677
      · exact prime_quadB_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 269456833) ^ 134728416 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 269456833) ^ 89818944 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 269456833) ^ 398016 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 269456833) ^ 389952 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_282045737 : Nat.Prime 282045737 := by
  apply lucas_primality 282045737 (3 : ZMod 282045737)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod = 282045737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_97
      · exact prime_quadB_137
      · exact prime_quadB_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 282045737) ^ 141022868 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 40292248 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2907688 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2058728 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 744184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_634614601 : Nat.Prime 634614601 := by
  apply lucas_primality 634614601 (14 : ZMod 634614601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (389, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (389, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod = 634614601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_389
      · exact prime_quadB_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 634614601) ^ 317307300 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 634614601) ^ 211538200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 634614601) ^ 126922920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 634614601) ^ 1631400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 634614601) ^ 233400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_322268741 : Nat.Prime 322268741 := by
  apply lucas_primality 322268741 (2 : ZMod 322268741)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (211, 1), (76367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (211, 1), (76367, 1)] : List FactorBlock).map factorBlockValue).prod = 322268741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_211
      · exact prime_quadB_76367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 322268741) ^ 161134370 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 322268741) ^ 64453748 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 322268741) ^ 1527340 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 322268741) ^ 4220 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_644537483 : Nat.Prime 644537483 := by
  apply lucas_primality 644537483 (2 : ZMod 644537483)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (322268741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (322268741, 1)] : List FactorBlock).map factorBlockValue).prod = 644537483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_322268741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 644537483) ^ 322268741 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 644537483) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_820766489 : Nat.Prime 820766489 := by
  apply lucas_primality 820766489 (3 : ZMod 820766489)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (733, 1), (139967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (733, 1), (139967, 1)] : List FactorBlock).map factorBlockValue).prod = 820766489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_733
      · exact prime_quadB_139967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 820766489) ^ 410383244 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 820766489) ^ 1119736 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 820766489) ^ 5864 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1130858507 : Nat.Prime 1130858507 := by
  apply lucas_primality 1130858507 (2 : ZMod 1130858507)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5059, 1), (111767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5059, 1), (111767, 1)] : List FactorBlock).map factorBlockValue).prod = 1130858507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5059
      · exact prime_quadB_111767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1130858507) ^ 565429253 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130858507) ^ 223534 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130858507) ^ 10118 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_29
      · exact prime_quadB_113
      · exact prime_quadB_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_17
      · exact prime_quadB_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3344266327 : Nat.Prime 3344266327 := by
  apply lucas_primality 3344266327 (5 : ZMod 3344266327)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (821, 1), (678901, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (821, 1), (678901, 1)] : List FactorBlock).map factorBlockValue).prod = 3344266327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_821
      · exact prime_quadB_678901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3344266327) ^ 1672133163 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3344266327) ^ 1114755442 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3344266327) ^ 4073406 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3344266327) ^ 4926 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_5471890517 : Nat.Prime 5471890517 := by
  apply lucas_primality 5471890517 (2 : ZMod 5471890517)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (659, 1), (2075831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (659, 1), (2075831, 1)] : List FactorBlock).map factorBlockValue).prod = 5471890517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_659
      · exact prime_quadB_2075831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5471890517) ^ 2735945258 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 5471890517) ^ 8303324 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 5471890517) ^ 2636 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1407433327 : Nat.Prime 1407433327 := by
  apply lucas_primality 1407433327 (3 : ZMod 1407433327)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (18044017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (18044017, 1)] : List FactorBlock).map factorBlockValue).prod = 1407433327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_13
      · exact prime_quadB_18044017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1407433327) ^ 703716663 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407433327) ^ 469144442 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407433327) ^ 108264102 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407433327) ^ 78 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_8444599963 : Nat.Prime 8444599963 := by
  apply lucas_primality 8444599963 (5 : ZMod 8444599963)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1407433327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1407433327, 1)] : List FactorBlock).map factorBlockValue).prod = 8444599963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_1407433327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8444599963) ^ 4222299981 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 8444599963) ^ 2814866654 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 8444599963) ^ 6 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_11249727107 : Nat.Prime 11249727107 := by
  apply lucas_primality 11249727107 (2 : ZMod 11249727107)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (709, 1), (149689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (709, 1), (149689, 1)] : List FactorBlock).map factorBlockValue).prod = 11249727107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_53
      · exact prime_quadB_709
      · exact prime_quadB_149689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11249727107) ^ 5624863553 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 11249727107) ^ 212259002 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 11249727107) ^ 15867034 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 11249727107) ^ 75154 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_23
      · exact prime_quadB_47
      · exact prime_quadB_59
      · exact prime_quadB_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_15868964827 : Nat.Prime 15868964827 := by
  apply lucas_primality 15868964827 (2 : ZMod 15868964827)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (11, 1), (13, 1), (228337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (11, 1), (13, 1), (228337, 1)] : List FactorBlock).map factorBlockValue).prod = 15868964827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_228337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15868964827) ^ 7934482413 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 15868964827) ^ 5289654942 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 15868964827) ^ 1442633166 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 15868964827) ^ 1220689602 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 15868964827) ^ 69498 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_28653985897 : Nat.Prime 28653985897 := by
  apply lucas_primality 28653985897 (10 : ZMod 28653985897)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (151, 1), (7906729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (151, 1), (7906729, 1)] : List FactorBlock).map factorBlockValue).prod = 28653985897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_151
      · exact prime_quadB_7906729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 28653985897) ^ 14326992948 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 28653985897) ^ 9551328632 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 28653985897) ^ 189761496 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 28653985897) ^ 3624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_30384297329 : Nat.Prime 30384297329 := by
  apply lucas_primality 30384297329 (3 : ZMod 30384297329)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod = 30384297329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_1709
      · exact prime_quadB_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30384297329) ^ 15192148664 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 4340613904 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2762208848 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 17778992 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2105488 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_739651207 : Nat.Prime 739651207 := by
  apply lucas_primality 739651207 (3 : ZMod 739651207)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (29, 1), (263, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (29, 1), (263, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod = 739651207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_29
      · exact prime_quadB_263
      · exact prime_quadB_2309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 739651207) ^ 369825603 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 739651207) ^ 246550402 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 739651207) ^ 105664458 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 739651207) ^ 25505214 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 739651207) ^ 2812362 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 739651207) ^ 320334 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_47337677249 : Nat.Prime 47337677249 := by
  apply lucas_primality 47337677249 (3 : ZMod 47337677249)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (739651207, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (739651207, 1)] : List FactorBlock).map factorBlockValue).prod = 47337677249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_739651207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 47337677249) ^ 23668838624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 47337677249) ^ 64 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_33107719 : Nat.Prime 33107719 := by
  apply lucas_primality 33107719 (7 : ZMod 33107719)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod = 33107719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_23
      · exact prime_quadB_34273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33107719) ^ 16553859 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 33107719) ^ 11035906 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 33107719) ^ 4729674 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 33107719) ^ 1439466 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 33107719) ^ 966 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_69857287091 : Nat.Prime 69857287091 := by
  apply lucas_primality 69857287091 (2 : ZMod 69857287091)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (211, 1), (33107719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (211, 1), (33107719, 1)] : List FactorBlock).map factorBlockValue).prod = 69857287091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_211
      · exact prime_quadB_33107719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69857287091) ^ 34928643545 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 69857287091) ^ 13971457418 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 69857287091) ^ 331077190 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 69857287091) ^ 2110 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_110719776691 : Nat.Prime 110719776691 := by
  apply lucas_primality 110719776691 (10 : ZMod 110719776691)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (2897, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (2897, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod = 110719776691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_2897
      · exact prime_quadB_141551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 110719776691) ^ 55359888345 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 36906592230 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 22143955338 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 38218770 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 110719776691) ^ 782190 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_91452329 : Nat.Prime 91452329 := by
  apply lucas_primality 91452329 (3 : ZMod 91452329)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (191, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod = 91452329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_191
      · exact prime_quadB_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91452329) ^ 45726164 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 8313848 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 478808 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 91452329) ^ 16808 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_199731886537 : Nat.Prime 199731886537 := by
  apply lucas_primality 199731886537 (10 : ZMod 199731886537)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (13, 1), (91452329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (13, 1), (91452329, 1)] : List FactorBlock).map factorBlockValue).prod = 199731886537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_91452329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 199731886537) ^ 99865943268 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 66577295512 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 28533126648 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 15363991272 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 199731886537) ^ 2184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_160736592539 : Nat.Prime 160736592539 := by
  apply lucas_primality 160736592539 (2 : ZMod 160736592539)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod = 160736592539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_29
      · exact prime_quadB_49627
      · exact prime_quadB_55843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160736592539) ^ 80368296269 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 5542641122 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 3238894 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 2878366 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_321473185079 : Nat.Prime 321473185079 := by
  apply lucas_primality 321473185079 (7 : ZMod 321473185079)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod = 321473185079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_160736592539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 321473185079) ^ 160736592539 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 321473185079) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_400597142329 : Nat.Prime 400597142329 := by
  apply lucas_primality 400597142329 (11 : ZMod 400597142329)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod = 400597142329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_17
      · exact prime_quadB_41
      · exact prime_quadB_7982567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 400597142329) ^ 200298571164 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 133532380776 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 23564537784 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 9770662008 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 400597142329) ^ 50184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_492016319777 : Nat.Prime 492016319777 := by
  apply lucas_primality 492016319777 (3 : ZMod 492016319777)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (947, 1), (16236019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (947, 1), (16236019, 1)] : List FactorBlock).map factorBlockValue).prod = 492016319777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_947
      · exact prime_quadB_16236019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 492016319777) ^ 246008159888 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 492016319777) ^ 519552608 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 492016319777) ^ 30304 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_90007433 : Nat.Prime 90007433 := by
  apply lucas_primality 90007433 (3 : ZMod 90007433)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11250929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11250929, 1)] : List FactorBlock).map factorBlockValue).prod = 90007433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11250929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 90007433) ^ 45003716 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 90007433) ^ 8 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_180014867 : Nat.Prime 180014867 := by
  apply lucas_primality 180014867 (2 : ZMod 180014867)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (90007433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (90007433, 1)] : List FactorBlock).map factorBlockValue).prod = 180014867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_90007433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 180014867) ^ 90007433 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 180014867) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_573887395997 : Nat.Prime 573887395997 := by
  apply lucas_primality 573887395997 (2 : ZMod 573887395997)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (797, 1), (180014867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (797, 1), (180014867, 1)] : List FactorBlock).map factorBlockValue).prod = 573887395997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_797
      · exact prime_quadB_180014867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 573887395997) ^ 286943697998 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 573887395997) ^ 720059468 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 573887395997) ^ 3188 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_739
      · exact prime_quadB_1307
      · exact prime_quadB_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_850971844357 : Nat.Prime 850971844357 := by
  apply lucas_primality 850971844357 (2 : ZMod 850971844357)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (1489, 1), (1107569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (1489, 1), (1107569, 1)] : List FactorBlock).map factorBlockValue).prod = 850971844357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_43
      · exact prime_quadB_1489
      · exact prime_quadB_1107569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 850971844357) ^ 425485922178 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 850971844357) ^ 283657281452 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 850971844357) ^ 19790042892 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 850971844357) ^ 571505604 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 850971844357) ^ 768324 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_26368157 : Nat.Prime 26368157 := by
  apply lucas_primality 26368157 (2 : ZMod 26368157)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (401, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (401, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod = 26368157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_401
      · exact prime_quadB_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26368157) ^ 13184078 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 26368157) ^ 1551068 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 26368157) ^ 65756 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 26368157) ^ 27268 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_972563102789 : Nat.Prime 972563102789 := by
  apply lucas_primality 972563102789 (2 : ZMod 972563102789)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (9221, 1), (26368157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (9221, 1), (26368157, 1)] : List FactorBlock).map factorBlockValue).prod = 972563102789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_9221
      · exact prime_quadB_26368157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 972563102789) ^ 486281551394 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 972563102789) ^ 105472628 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 972563102789) ^ 36884 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1357034643673 : Nat.Prime 1357034643673 := by
  apply lucas_primality 1357034643673 (5 : ZMod 1357034643673)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod = 1357034643673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_83
      · exact prime_quadB_2269
      · exact prime_quadB_300239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1357034643673) ^ 678517321836 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 452344881224 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 16349814984 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 598076088 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 4519848 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3256364927 : Nat.Prime 3256364927 := by
  apply lucas_primality 3256364927 (5 : ZMod 3256364927)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (419, 1), (228581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (419, 1), (228581, 1)] : List FactorBlock).map factorBlockValue).prod = 3256364927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_419
      · exact prime_quadB_228581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3256364927) ^ 1628182463 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3256364927) ^ 191550878 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3256364927) ^ 7771754 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 3256364927) ^ 14246 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1432800567881 : Nat.Prime 1432800567881 := by
  apply lucas_primality 1432800567881 (6 : ZMod 1432800567881)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (3256364927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (3256364927, 1)] : List FactorBlock).map factorBlockValue).prod = 1432800567881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_3256364927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1432800567881) ^ 716400283940 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432800567881) ^ 286560113576 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432800567881) ^ 130254597080 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432800567881) ^ 440 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_23
      · exact prime_quadB_9739
      · exact prime_quadB_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2543333740247 : Nat.Prime 2543333740247 := by
  apply lucas_primality 2543333740247 (5 : ZMod 2543333740247)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (251, 1), (10867, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (251, 1), (10867, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod = 2543333740247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_13
      · exact prime_quadB_251
      · exact prime_quadB_10867
      · exact prime_quadB_35863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2543333740247) ^ 1271666870123 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2543333740247) ^ 195641056942 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2543333740247) ^ 10132803746 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2543333740247) ^ 234041938 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2543333740247) ^ 70918042 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_137653927 : Nat.Prime 137653927 := by
  apply lucas_primality 137653927 (3 : ZMod 137653927)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod = 137653927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_4013
      · exact prime_quadB_5717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137653927) ^ 68826963 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 45884642 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 34302 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 24078 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4887540332063 : Nat.Prime 4887540332063 := by
  apply lucas_primality 4887540332063 (5 : ZMod 4887540332063)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod = 4887540332063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_41
      · exact prime_quadB_433
      · exact prime_quadB_137653927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4887540332063) ^ 2443770166031 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 119208300782 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 11287622014 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 35506 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_869680995581 : Nat.Prime 869680995581 := by
  apply lucas_primality 869680995581 (2 : ZMod 869680995581)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3769, 1), (11537291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3769, 1), (11537291, 1)] : List FactorBlock).map factorBlockValue).prod = 869680995581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_3769
      · exact prime_quadB_11537291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 869680995581) ^ 434840497790 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 869680995581) ^ 173936199116 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 869680995581) ^ 230745820 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 869680995581) ^ 75380 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_5218085973487 : Nat.Prime 5218085973487 := by
  apply lucas_primality 5218085973487 (3 : ZMod 5218085973487)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (869680995581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (869680995581, 1)] : List FactorBlock).map factorBlockValue).prod = 5218085973487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_869680995581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5218085973487) ^ 2609042986743 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 5218085973487) ^ 1739361991162 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 5218085973487) ^ 6 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_953935928321 : Nat.Prime 953935928321 := by
  apply lucas_primality 953935928321 (3 : ZMod 953935928321)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 10), (5, 1), (31, 1), (443, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 10), (5, 1), (31, 1), (443, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod = 953935928321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_31
      · exact prime_quadB_443
      · exact prime_quadB_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 953935928321) ^ 476967964160 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 953935928321) ^ 190787185664 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 953935928321) ^ 30772126720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 953935928321) ^ 2153354240 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 953935928321) ^ 70312960 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_7631487426569 : Nat.Prime 7631487426569 := by
  apply lucas_primality 7631487426569 (3 : ZMod 7631487426569)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (953935928321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (953935928321, 1)] : List FactorBlock).map factorBlockValue).prod = 7631487426569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_953935928321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7631487426569) ^ 3815743713284 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 7631487426569) ^ 8 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_10158661475129 : Nat.Prime 10158661475129 := by
  apply lucas_primality 10158661475129 (3 : ZMod 10158661475129)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (211, 1), (599, 1), (1091, 1), (9209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (211, 1), (599, 1), (1091, 1), (9209, 1)] : List FactorBlock).map factorBlockValue).prod = 10158661475129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_211
      · exact prime_quadB_599
      · exact prime_quadB_1091
      · exact prime_quadB_9209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10158661475129) ^ 5079330737564 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158661475129) ^ 48145315048 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158661475129) ^ 16959368072 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158661475129) ^ 9311330408 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158661475129) ^ 1103123192 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4994455709 : Nat.Prime 4994455709 := by
  apply lucas_primality 4994455709 (2 : ZMod 4994455709)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (3323, 1), (34159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (3323, 1), (34159, 1)] : List FactorBlock).map factorBlockValue).prod = 4994455709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_3323
      · exact prime_quadB_34159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4994455709) ^ 2497227854 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4994455709) ^ 454041428 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4994455709) ^ 1502996 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4994455709) ^ 146212 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_17770273412623 : Nat.Prime 17770273412623 := by
  apply lucas_primality 17770273412623 (3 : ZMod 17770273412623)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (593, 1), (4994455709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (593, 1), (4994455709, 1)] : List FactorBlock).map factorBlockValue).prod = 17770273412623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_593
      · exact prime_quadB_4994455709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17770273412623) ^ 8885136706311 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 17770273412623) ^ 5923424470874 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 17770273412623) ^ 29966734254 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 17770273412623) ^ 3558 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_23314525201361 : Nat.Prime 23314525201361 := by
  apply lucas_primality 23314525201361 (3 : ZMod 23314525201361)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (67, 1), (233, 1), (673, 1), (27739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (67, 1), (233, 1), (673, 1), (27739, 1)] : List FactorBlock).map factorBlockValue).prod = 23314525201361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_67
      · exact prime_quadB_233
      · exact prime_quadB_673
      · exact prime_quadB_27739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23314525201361) ^ 11657262600680 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 23314525201361) ^ 4662905040272 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 23314525201361) ^ 347977988080 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 23314525201361) ^ 100062339920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 23314525201361) ^ 34642682320 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 23314525201361) ^ 840496240 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_150767581 : Nat.Prime 150767581 := by
  apply lucas_primality 150767581 (6 : ZMod 150767581)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1511, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1511, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod = 150767581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_1511
      · exact prime_quadB_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 150767581) ^ 75383790 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 150767581) ^ 50255860 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 150767581) ^ 30153516 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 150767581) ^ 99780 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 150767581) ^ 90660 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_25179392167649 : Nat.Prime 25179392167649 := by
  apply lucas_primality 25179392167649 (3 : ZMod 25179392167649)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (17, 1), (307, 1), (150767581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (17, 1), (307, 1), (150767581, 1)] : List FactorBlock).map factorBlockValue).prod = 25179392167649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_307
      · exact prime_quadB_150767581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25179392167649) ^ 12589696083824 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 25179392167649) ^ 1481140715744 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 25179392167649) ^ 82017564064 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 25179392167649) ^ 167008 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_29
      · exact prime_quadB_34361
      · exact prime_quadB_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_23
      · exact prime_quadB_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_24195499 : Nat.Prime 24195499 := by
  apply lucas_primality 24195499 (2 : ZMod 24195499)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (191, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (191, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod = 24195499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_43
      · exact prime_quadB_191
      · exact prime_quadB_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24195499) ^ 12097749 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 8065166 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 562686 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 126678 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 49278 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_37214467928927 : Nat.Prime 37214467928927 := by
  apply lucas_primality 37214467928927 (5 : ZMod 37214467928927)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod = 37214467928927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_41
      · exact prime_quadB_18757
      · exact prime_quadB_24195499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37214467928927) ^ 18607233964463 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 907669949486 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1984030918 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1538074 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_67
      · exact prime_quadB_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_89
      · exact prime_quadB_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_153937759 : Nat.Prime 153937759 := by
  apply lucas_primality 153937759 (3 : ZMod 153937759)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (23, 1), (53, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (23, 1), (53, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod = 153937759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_13
      · exact prime_quadB_23
      · exact prime_quadB_53
      · exact prime_quadB_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 153937759) ^ 76968879 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 153937759) ^ 51312586 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 153937759) ^ 11841366 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 153937759) ^ 6692946 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 153937759) ^ 2904486 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 153937759) ^ 95082 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_87160790647873 : Nat.Prime 87160790647873 := by
  apply lucas_primality 87160790647873 (5 : ZMod 87160790647873)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (983, 1), (153937759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (983, 1), (153937759, 1)] : List FactorBlock).map factorBlockValue).prod = 87160790647873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_983
      · exact prime_quadB_153937759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 87160790647873) ^ 43580395323936 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 87160790647873) ^ 29053596882624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 87160790647873) ^ 88668149184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 87160790647873) ^ 566208 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_9091566749 : Nat.Prime 9091566749 := by
  apply lucas_primality 9091566749 (3 : ZMod 9091566749)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (17, 1), (12154501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (17, 1), (12154501, 1)] : List FactorBlock).map factorBlockValue).prod = 9091566749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_17
      · exact prime_quadB_12154501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9091566749) ^ 4545783374 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 9091566749) ^ 826506068 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 9091566749) ^ 534798044 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 9091566749) ^ 748 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_167357560715593 : Nat.Prime 167357560715593 := by
  apply lucas_primality 167357560715593 (5 : ZMod 167357560715593)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (59, 1), (9091566749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (59, 1), (9091566749, 1)] : List FactorBlock).map factorBlockValue).prod = 167357560715593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_13
      · exact prime_quadB_59
      · exact prime_quadB_9091566749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 167357560715593) ^ 83678780357796 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 167357560715593) ^ 55785853571864 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 167357560715593) ^ 12873658516584 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 167357560715593) ^ 2836568825688 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 167357560715593) ^ 18408 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_82349327 : Nat.Prime 82349327 := by
  apply lucas_primality 82349327 (5 : ZMod 82349327)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (157, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (157, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod = 82349327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_157
      · exact prime_quadB_15427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 82349327) ^ 41174663 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 82349327) ^ 4844078 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 82349327) ^ 524518 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 82349327) ^ 5338 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_207486376117277 : Nat.Prime 207486376117277 := by
  apply lucas_primality 207486376117277 (2 : ZMod 207486376117277)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (629897, 1), (82349327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (629897, 1), (82349327, 1)] : List FactorBlock).map factorBlockValue).prod = 207486376117277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_629897
      · exact prime_quadB_82349327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 207486376117277) ^ 103743188058638 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 207486376117277) ^ 329397308 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 207486376117277) ^ 2519588 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_297806723575661 : Nat.Prime 297806723575661 := by
  apply lucas_primality 297806723575661 (2 : ZMod 297806723575661)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (541, 1), (7477, 1), (283163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (541, 1), (7477, 1), (283163, 1)] : List FactorBlock).map factorBlockValue).prod = 297806723575661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_541
      · exact prime_quadB_7477
      · exact prime_quadB_283163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 297806723575661) ^ 148903361787830 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 297806723575661) ^ 59561344715132 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 297806723575661) ^ 22908209505820 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 297806723575661) ^ 550474535260 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 297806723575661) ^ 39829707580 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 297806723575661) ^ 1051714820 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_75571277 : Nat.Prime 75571277 := by
  apply lucas_primality 75571277 (2 : ZMod 75571277)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 2), (156139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 2), (156139, 1)] : List FactorBlock).map factorBlockValue).prod = 75571277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_156139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75571277) ^ 37785638 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 75571277) ^ 6870116 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 75571277) ^ 484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_369954349991773 : Nat.Prime 369954349991773 := by
  apply lucas_primality 369954349991773 (5 : ZMod 369954349991773)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (13, 1), (4483, 1), (75571277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (13, 1), (4483, 1), (75571277, 1)] : List FactorBlock).map factorBlockValue).prod = 369954349991773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_4483
      · exact prime_quadB_75571277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 369954349991773) ^ 184977174995886 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 123318116663924 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 52850621427396 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 28458026922444 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 82523834484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 369954349991773) ^ 4895436 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_983
      · exact prime_quadB_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3689544277 : Nat.Prime 3689544277 := by
  apply lucas_primality 3689544277 (2 : ZMod 3689544277)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (11, 1), (139, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (11, 1), (139, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod = 3689544277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_11
      · exact prime_quadB_139
      · exact prime_quadB_22343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3689544277) ^ 1844772138 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689544277) ^ 1229848092 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689544277) ^ 335413116 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689544277) ^ 26543484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689544277) ^ 165132 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_413450331680621 : Nat.Prime 413450331680621 := by
  apply lucas_primality 413450331680621 (2 : ZMod 413450331680621)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (431, 1), (3689544277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (431, 1), (3689544277, 1)] : List FactorBlock).map factorBlockValue).prod = 413450331680621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_431
      · exact prime_quadB_3689544277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 413450331680621) ^ 206725165840310 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 413450331680621) ^ 82690066336124 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 413450331680621) ^ 31803871667740 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 413450331680621) ^ 959281512020 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 413450331680621) ^ 112060 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_633877705653067 : Nat.Prime 633877705653067 := by
  apply lucas_primality 633877705653067 (2 : ZMod 633877705653067)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (107, 1), (37397, 1), (1257229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (107, 1), (37397, 1), (1257229, 1)] : List FactorBlock).map factorBlockValue).prod = 633877705653067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_107
      · exact prime_quadB_37397
      · exact prime_quadB_1257229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 633877705653067) ^ 316938852826533 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 633877705653067) ^ 211292568551022 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 633877705653067) ^ 90553957950438 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 633877705653067) ^ 5924090707038 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 633877705653067) ^ 16949961378 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 633877705653067) ^ 504186354 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2024581991983 : Nat.Prime 2024581991983 := by
  apply lucas_primality 2024581991983 (3 : ZMod 2024581991983)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod = 2024581991983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_11
      · exact prime_quadB_6997
      · exact prime_quadB_4384091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2024581991983) ^ 1012290995991 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 674860663994 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 184052908362 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 289350006 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 461802 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_700505369226119 : Nat.Prime 700505369226119 := by
  apply lucas_primality 700505369226119 (7 : ZMod 700505369226119)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod = 700505369226119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_173
      · exact prime_quadB_2024581991983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 700505369226119) ^ 350252684613059 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 4049163983966 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 346 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_45749372969 : Nat.Prime 45749372969 := by
  apply lucas_primality 45749372969 (3 : ZMod 45749372969)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (5443, 1), (80819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (5443, 1), (80819, 1)] : List FactorBlock).map factorBlockValue).prod = 45749372969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_13
      · exact prime_quadB_5443
      · exact prime_quadB_80819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45749372969) ^ 22874686484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 45749372969) ^ 3519182536 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 45749372969) ^ 8405176 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 45749372969) ^ 566072 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_753034679069741 : Nat.Prime 753034679069741 := by
  apply lucas_primality 753034679069741 (2 : ZMod 753034679069741)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (823, 1), (45749372969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (823, 1), (45749372969, 1)] : List FactorBlock).map factorBlockValue).prod = 753034679069741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_823
      · exact prime_quadB_45749372969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 753034679069741) ^ 376517339534870 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 753034679069741) ^ 150606935813948 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 753034679069741) ^ 914987459380 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 753034679069741) ^ 16460 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1506069358139483 : Nat.Prime 1506069358139483 := by
  apply lucas_primality 1506069358139483 (2 : ZMod 1506069358139483)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (753034679069741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (753034679069741, 1)] : List FactorBlock).map factorBlockValue).prod = 1506069358139483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_753034679069741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1506069358139483) ^ 753034679069741 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506069358139483) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_669453569 : Nat.Prime 669453569 := by
  apply lucas_primality 669453569 (3 : ZMod 669453569)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (7, 1), (167, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (7, 1), (167, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod = 669453569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_167
      · exact prime_quadB_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 669453569) ^ 334726784 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 669453569) ^ 95636224 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 669453569) ^ 4008704 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 669453569) ^ 299264 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_319555627719323 : Nat.Prime 319555627719323 := by
  apply lucas_primality 319555627719323 (2 : ZMod 319555627719323)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (7699, 1), (669453569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (7699, 1), (669453569, 1)] : List FactorBlock).map factorBlockValue).prod = 319555627719323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_31
      · exact prime_quadB_7699
      · exact prime_quadB_669453569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 319555627719323) ^ 159777813859661 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 319555627719323) ^ 10308246055462 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 319555627719323) ^ 41506121278 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 319555627719323) ^ 477338 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1917333766315939 : Nat.Prime 1917333766315939 := by
  apply lucas_primality 1917333766315939 (2 : ZMod 1917333766315939)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (319555627719323, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (319555627719323, 1)] : List FactorBlock).map factorBlockValue).prod = 1917333766315939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_319555627719323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1917333766315939) ^ 958666883157969 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917333766315939) ^ 639111255438646 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917333766315939) ^ 6 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_29623871 : Nat.Prime 29623871 := by
  apply lucas_primality 29623871 (7 : ZMod 29623871)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod = 29623871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_409
      · exact prime_quadB_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29623871) ^ 14811935 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 5924774 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 72430 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 4090 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_59247743 : Nat.Prime 59247743 := by
  apply lucas_primality 59247743 (5 : ZMod 59247743)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod = 59247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_29623871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59247743) ^ 29623871 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 59247743) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2743295750628703 : Nat.Prime 2743295750628703 := by
  apply lucas_primality 2743295750628703 (5 : ZMod 2743295750628703)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod = 2743295750628703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_2531
      · exact prime_quadB_3049
      · exact prime_quadB_59247743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2743295750628703) ^ 1371647875314351 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 914431916876234 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 1083878210442 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 899736225198 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 46302114 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_151677853 : Nat.Prime 151677853 := by
  apply lucas_primality 151677853 (2 : ZMod 151677853)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod = 151677853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_83
      · exact prime_quadB_152287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151677853) ^ 75838926 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 50559284 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 1827444 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 996 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4496625855541289 : Nat.Prime 4496625855541289 := by
  apply lucas_primality 4496625855541289 (3 : ZMod 4496625855541289)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod = 4496625855541289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_23
      · exact prime_quadB_23017
      · exact prime_quadB_151677853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4496625855541289) ^ 2248312927770644 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 642375122220184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 195505471980056 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 195361074664 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 29645896 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_936013643 : Nat.Prime 936013643 := by
  apply lucas_primality 936013643 (2 : ZMod 936013643)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (37, 1), (59, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (37, 1), (59, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod = 936013643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_37
      · exact prime_quadB_59
      · exact prime_quadB_12611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 936013643) ^ 468006821 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 936013643) ^ 55059626 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 936013643) ^ 25297666 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 936013643) ^ 15864638 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 936013643) ^ 74222 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1398404382643 : Nat.Prime 1398404382643 := by
  apply lucas_primality 1398404382643 (3 : ZMod 1398404382643)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (83, 1), (936013643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (83, 1), (936013643, 1)] : List FactorBlock).map factorBlockValue).prod = 1398404382643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_83
      · exact prime_quadB_936013643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1398404382643) ^ 699202191321 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398404382643) ^ 466134794214 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398404382643) ^ 16848245574 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398404382643) ^ 1494 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_13094658639069053 : Nat.Prime 13094658639069053 := by
  apply lucas_primality 13094658639069053 (2 : ZMod 13094658639069053)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2341, 1), (1398404382643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2341, 1), (1398404382643, 1)] : List FactorBlock).map factorBlockValue).prod = 13094658639069053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_2341
      · exact prime_quadB_1398404382643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13094658639069053) ^ 6547329319534526 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 13094658639069053) ^ 5593617530572 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 13094658639069053) ^ 9364 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_1901
      · exact prime_quadB_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_384973
      · exact prime_quadB_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_41734093 : Nat.Prime 41734093 := by
  apply lucas_primality 41734093 (2 : ZMod 41734093)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod = 41734093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41734093) ^ 20867046 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 13911364 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 12 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_82299631397 : Nat.Prime 82299631397 := by
  apply lucas_primality 82299631397 (2 : ZMod 82299631397)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod = 82299631397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_29
      · exact prime_quadB_41734093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82299631397) ^ 41149815698 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 4841154788 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 2837918324 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 1972 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_493797788383 : Nat.Prime 493797788383 := by
  apply lucas_primality 493797788383 (3 : ZMod 493797788383)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod = 493797788383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_82299631397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 493797788383) ^ 246898894191 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 164599262794 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 6 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4937977883831 : Nat.Prime 4937977883831 := by
  apply lucas_primality 4937977883831 (11 : ZMod 4937977883831)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod = 4937977883831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_493797788383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4937977883831) ^ 2468988941915 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 987595576766 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 10 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_190813341386997503 : Nat.Prime 190813341386997503 := by
  apply lucas_primality 190813341386997503 (5 : ZMod 190813341386997503)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod = 190813341386997503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_139
      · exact prime_quadB_4937977883831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190813341386997503) ^ 95406670693498751 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 1372757851705018 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 38642 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_16103786791 : Nat.Prime 16103786791 := by
  apply lucas_primality 16103786791 (7 : ZMod 16103786791)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod = 16103786791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_569
      · exact prime_quadB_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16103786791) ^ 8051893395 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 5367928930 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 3220757358 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 2300540970 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 1238752830 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 28301910 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 10873590 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_284004322561366753 : Nat.Prime 284004322561366753 := by
  apply lucas_primality 284004322561366753 (5 : ZMod 284004322561366753)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod = 284004322561366753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_183707
      · exact prime_quadB_16103786791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284004322561366753) ^ 142002161280683376 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 94668107520455584 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 1545963531936 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 17635872 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_5037757
      · exact prime_quadB_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_73483933 : Nat.Prime 73483933 := by
  apply lucas_primality 73483933 (2 : ZMod 73483933)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1879, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1879, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod = 73483933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_1879
      · exact prime_quadB_3259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73483933) ^ 36741966 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483933) ^ 24494644 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483933) ^ 39108 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483933) ^ 22548 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_34914148019994973 : Nat.Prime 34914148019994973 := by
  apply lucas_primality 34914148019994973 (14 : ZMod 34914148019994973)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1033, 1), (38329, 1), (73483933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1033, 1), (38329, 1), (73483933, 1)] : List FactorBlock).map factorBlockValue).prod = 34914148019994973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_1033
      · exact prime_quadB_38329
      · exact prime_quadB_73483933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 34914148019994973) ^ 17457074009997486 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 34914148019994973) ^ 11638049339998324 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 34914148019994973) ^ 33798788015484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 34914148019994973) ^ 910906833468 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 34914148019994973) ^ 475126284 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_418969776239939677 : Nat.Prime 418969776239939677 := by
  apply lucas_primality 418969776239939677 (6 : ZMod 418969776239939677)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (34914148019994973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (34914148019994973, 1)] : List FactorBlock).map factorBlockValue).prod = 418969776239939677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_34914148019994973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 418969776239939677) ^ 209484888119969838 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 418969776239939677) ^ 139656592079979892 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 418969776239939677) ^ 12 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_397
      · exact prime_quadB_2531
      · exact prime_quadB_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_41
      · exact prime_quadB_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_29
      · exact prime_quadB_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_798921867787 : Nat.Prime 798921867787 := by
  apply lucas_primality 798921867787 (3 : ZMod 798921867787)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (23, 1), (317, 1), (372709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (23, 1), (317, 1), (372709, 1)] : List FactorBlock).map factorBlockValue).prod = 798921867787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_23
      · exact prime_quadB_317
      · exact prime_quadB_372709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 798921867787) ^ 399460933893 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 798921867787) ^ 266307289262 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 798921867787) ^ 114131695398 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 798921867787) ^ 34735733382 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 798921867787) ^ 2520258258 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 798921867787) ^ 2143554 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_606490351024352033 : Nat.Prime 606490351024352033 := by
  apply lucas_primality 606490351024352033 (3 : ZMod 606490351024352033)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (3389, 1), (798921867787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (3389, 1), (798921867787, 1)] : List FactorBlock).map factorBlockValue).prod = 606490351024352033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_3389
      · exact prime_quadB_798921867787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 606490351024352033) ^ 303245175512176016 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 606490351024352033) ^ 86641478717764576 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 606490351024352033) ^ 178958498384288 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 606490351024352033) ^ 759136 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_15863065847 : Nat.Prime 15863065847 := by
  apply lucas_primality 15863065847 (5 : ZMod 15863065847)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (727, 1), (10909949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (727, 1), (10909949, 1)] : List FactorBlock).map factorBlockValue).prod = 15863065847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_727
      · exact prime_quadB_10909949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15863065847) ^ 7931532923 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 15863065847) ^ 21819898 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 15863065847) ^ 1454 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1165261096003739113 : Nat.Prime 1165261096003739113 := by
  apply lucas_primality 1165261096003739113 (13 : ZMod 1165261096003739113)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (7, 1), (19, 1), (2557, 1), (15863065847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (7, 1), (19, 1), (2557, 1), (15863065847, 1)] : List FactorBlock).map factorBlockValue).prod = 1165261096003739113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_19
      · exact prime_quadB_2557
      · exact prime_quadB_15863065847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1165261096003739113) ^ 582630548001869556 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165261096003739113) ^ 388420365334579704 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165261096003739113) ^ 166465870857677016 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165261096003739113) ^ 61329531368617848 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165261096003739113) ^ 455714155652616 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165261096003739113) ^ 73457496 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_469486855561 : Nat.Prime 469486855561 := by
  apply lucas_primality 469486855561 (7 : ZMod 469486855561)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod = 469486855561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_251
      · exact prime_quadB_15587213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 469486855561) ^ 234743427780 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 156495618520 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 93897371112 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 1870465560 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 30120 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1625331568846003853 : Nat.Prime 1625331568846003853 := by
  apply lucas_primality 1625331568846003853 (2 : ZMod 1625331568846003853)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod = 1625331568846003853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_865483
      · exact prime_quadB_469486855561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1625331568846003853) ^ 812665784423001926 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625331568846003853) ^ 1877947422244 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625331568846003853) ^ 3461932 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_143826233 : Nat.Prime 143826233 := by
  apply lucas_primality 143826233 (3 : ZMod 143826233)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod = 143826233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_563
      · exact prime_quadB_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 143826233) ^ 71913116 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 13075112 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 255464 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 49544 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3030158014634483503 : Nat.Prime 3030158014634483503 := by
  apply lucas_primality 3030158014634483503 (3 : ZMod 3030158014634483503)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod = 3030158014634483503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_6514591
      · exact prime_quadB_143826233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3030158014634483503) ^ 1515079007317241751 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 1010052671544827834 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 432879716376354786 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 275468910421316682 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 465134037522 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 21068187294 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_28785499 : Nat.Prime 28785499 := by
  apply lucas_primality 28785499 (2 : ZMod 28785499)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod = 28785499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_685369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28785499) ^ 14392749 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 9595166 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 4112214 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 42 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_10496781784408483841 : Nat.Prime 10496781784408483841 := by
  apply lucas_primality 10496781784408483841 (3 : ZMod 10496781784408483841)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod = 10496781784408483841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_53
      · exact prime_quadB_671903
      · exact prime_quadB_28785499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10496781784408483841) ^ 5248390892204241920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 2099356356881696768 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 198052486498273280 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 15622466017280 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 364655196160 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_19
      · exact prime_quadB_1823
      · exact prime_quadB_3271
      · exact prime_quadB_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_67
      · exact prime_quadB_28807
      · exact prime_quadB_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_23
      · exact prime_quadB_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_757699031 : Nat.Prime 757699031 := by
  apply lucas_primality 757699031 (11 : ZMod 757699031)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (6888173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (6888173, 1)] : List FactorBlock).map factorBlockValue).prod = 757699031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_6888173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 757699031) ^ 378849515 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 151539806 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 68881730 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 757699031) ^ 110 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_504627554647 : Nat.Prime 504627554647 := by
  apply lucas_primality 504627554647 (3 : ZMod 504627554647)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (37, 1), (757699031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (37, 1), (757699031, 1)] : List FactorBlock).map factorBlockValue).prod = 504627554647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_37
      · exact prime_quadB_757699031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 504627554647) ^ 252313777323 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 168209184882 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 13638582558 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 504627554647) ^ 666 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_15012789852106255987 : Nat.Prime 15012789852106255987 := by
  apply lucas_primality 15012789852106255987 (3 : ZMod 15012789852106255987)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (17, 2), (19, 1), (43, 1), (504627554647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (17, 2), (19, 1), (43, 1), (504627554647, 1)] : List FactorBlock).map factorBlockValue).prod = 15012789852106255987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_43
      · exact prime_quadB_504627554647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15012789852106255987) ^ 7506394926053127993 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 5004263284035418662 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 2144684264586607998 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 883105285418015058 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 790146834321381894 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 349134647723401302 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 15012789852106255987) ^ 29750238 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_6930211399 : Nat.Prime 6930211399 := by
  apply lucas_primality 6930211399 (11 : ZMod 6930211399)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (17, 1), (1861, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (17, 1), (1861, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod = 6930211399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_11
      · exact prime_quadB_17
      · exact prime_quadB_1861
      · exact prime_quadB_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6930211399) ^ 3465105699 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 6930211399) ^ 2310070466 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 6930211399) ^ 630019218 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 6930211399) ^ 407659494 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 6930211399) ^ 3723918 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 6930211399) ^ 2088042 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_18032824680885579373 : Nat.Prime 18032824680885579373 := by
  apply lucas_primality 18032824680885579373 (5 : ZMod 18032824680885579373)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (23, 1), (9427753, 1), (6930211399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (23, 1), (9427753, 1), (6930211399, 1)] : List FactorBlock).map factorBlockValue).prod = 18032824680885579373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_23
      · exact prime_quadB_9427753
      · exact prime_quadB_6930211399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18032824680885579373) ^ 9016412340442789686 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 18032824680885579373) ^ 6010941560295193124 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 18032824680885579373) ^ 784035855690677364 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 18032824680885579373) ^ 1912738346124 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 18032824680885579373) ^ 2602059828 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_30440479 : Nat.Prime 30440479 := by
  apply lucas_primality 30440479 (11 : ZMod 30440479)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (349, 1), (14537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (349, 1), (14537, 1)] : List FactorBlock).map factorBlockValue).prod = 30440479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_349
      · exact prime_quadB_14537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 30440479) ^ 15220239 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 30440479) ^ 10146826 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 30440479) ^ 87222 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 30440479) ^ 2094 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_215473831 : Nat.Prime 215473831 := by
  apply lucas_primality 215473831 (3 : ZMod 215473831)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (50227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (50227, 1)] : List FactorBlock).map factorBlockValue).prod = 215473831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_50227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 215473831) ^ 107736915 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 215473831) ^ 71824610 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 215473831) ^ 43094766 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 215473831) ^ 19588530 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 215473831) ^ 16574910 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 215473831) ^ 4290 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_33963157677738943723 : Nat.Prime 33963157677738943723 := by
  apply lucas_primality 33963157677738943723 (2 : ZMod 33963157677738943723)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (863, 1), (30440479, 1), (215473831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (863, 1), (30440479, 1), (215473831, 1)] : List FactorBlock).map factorBlockValue).prod = 33963157677738943723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_863
      · exact prime_quadB_30440479
      · exact prime_quadB_215473831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33963157677738943723) ^ 16981578838869471861 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 33963157677738943723) ^ 11321052559246314574 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 33963157677738943723) ^ 39354759765630294 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 33963157677738943723) ^ 1115723496918 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 33963157677738943723) ^ 157620800262 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_32982869 : Nat.Prime 32982869 := by
  apply lucas_primality 32982869 (2 : ZMod 32982869)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod = 32982869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_271
      · exact prime_quadB_30427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32982869) ^ 16491434 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 121708 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 1084 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1385280499 : Nat.Prime 1385280499 := by
  apply lucas_primality 1385280499 (2 : ZMod 1385280499)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod = 1385280499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_32982869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1385280499) ^ 692640249 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 461760166 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 197897214 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 42 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_148978605984457 : Nat.Prime 148978605984457 := by
  apply lucas_primality 148978605984457 (10 : ZMod 148978605984457)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod = 148978605984457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_4481
      · exact prime_quadB_1385280499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 148978605984457) ^ 74489302992228 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 49659535328152 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 33246731976 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 107544 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_68933592817856129557 : Nat.Prime 68933592817856129557 := by
  apply lucas_primality 68933592817856129557 (2 : ZMod 68933592817856129557)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod = 68933592817856129557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_12853
      · exact prime_quadB_148978605984457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68933592817856129557) ^ 34466796408928064778 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 22977864272618709852 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 5363229815440452 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 462708 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_252913357496471033039 : Nat.Prime 252913357496471033039 := by
  apply lucas_primality 252913357496471033039 (13 : ZMod 252913357496471033039)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod = 252913357496471033039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_337
      · exact prime_quadB_601
      · exact prime_quadB_40739
      · exact prime_quadB_115901
      · exact prime_quadB_132233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 252913357496471033039) ^ 126456678748235516519 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 750484740345611374 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 420820894336890238 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 6208138577198042 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 2182149916708838 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 1912634194917086 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1038583763131 : Nat.Prime 1038583763131 := by
  apply lucas_primality 1038583763131 (2 : ZMod 1038583763131)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (61, 1), (1873, 1), (303007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (61, 1), (1873, 1), (303007, 1)] : List FactorBlock).map factorBlockValue).prod = 1038583763131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_61
      · exact prime_quadB_1873
      · exact prime_quadB_303007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1038583763131) ^ 519291881565 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038583763131) ^ 346194587710 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038583763131) ^ 207716752626 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038583763131) ^ 17025963330 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038583763131) ^ 554502810 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038583763131) ^ 3427590 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_134634454779847456417 : Nat.Prime 134634454779847456417 := by
  apply lucas_primality 134634454779847456417 (5 : ZMod 134634454779847456417)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (1350341, 1), (1038583763131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (1350341, 1), (1038583763131, 1)] : List FactorBlock).map factorBlockValue).prod = 134634454779847456417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_1350341
      · exact prime_quadB_1038583763131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 134634454779847456417) ^ 67317227389923728208 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 134634454779847456417) ^ 44878151593282485472 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 134634454779847456417) ^ 99704041260576 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 134634454779847456417) ^ 129632736 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_538537819119389825669 : Nat.Prime 538537819119389825669 := by
  apply lucas_primality 538537819119389825669 (2 : ZMod 538537819119389825669)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (134634454779847456417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (134634454779847456417, 1)] : List FactorBlock).map factorBlockValue).prod = 538537819119389825669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_134634454779847456417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 538537819119389825669) ^ 269268909559694912834 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 538537819119389825669) ^ 4 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_112799441 : Nat.Prime 112799441 := by
  apply lucas_primality 112799441 (3 : ZMod 112799441)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (13, 1), (108461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (13, 1), (108461, 1)] : List FactorBlock).map factorBlockValue).prod = 112799441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_108461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 112799441) ^ 56399720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 112799441) ^ 22559888 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 112799441) ^ 8676880 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 112799441) ^ 1040 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_31823669 : Nat.Prime 31823669 := by
  apply lucas_primality 31823669 (2 : ZMod 31823669)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7955917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7955917, 1)] : List FactorBlock).map factorBlockValue).prod = 31823669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7955917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31823669) ^ 15911834 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 31823669) ^ 4 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2673188197 : Nat.Prime 2673188197 := by
  apply lucas_primality 2673188197 (2 : ZMod 2673188197)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (31823669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (31823669, 1)] : List FactorBlock).map factorBlockValue).prod = 2673188197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_31823669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2673188197) ^ 1336594098 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 2673188197) ^ 891062732 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 2673188197) ^ 381884028 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 2673188197) ^ 84 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_106927527881 : Nat.Prime 106927527881 := by
  apply lucas_primality 106927527881 (3 : ZMod 106927527881)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (2673188197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (2673188197, 1)] : List FactorBlock).map factorBlockValue).prod = 106927527881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_2673188197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 106927527881) ^ 53463763940 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 106927527881) ^ 21385505576 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 106927527881) ^ 40 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1278504729483803739227 : Nat.Prime 1278504729483803739227 := by
  apply lucas_primality 1278504729483803739227 (2 : ZMod 1278504729483803739227)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (112799441, 1), (106927527881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (112799441, 1), (106927527881, 1)] : List FactorBlock).map factorBlockValue).prod = 1278504729483803739227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_53
      · exact prime_quadB_112799441
      · exact prime_quadB_106927527881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1278504729483803739227) ^ 639252364741901869613 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278504729483803739227) ^ 24122730744977429042 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278504729483803739227) ^ 11334317955386 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278504729483803739227) ^ 11956740746 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_451540223 : Nat.Prime 451540223 := by
  apply lucas_primality 451540223 (5 : ZMod 451540223)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (859, 1), (37547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (859, 1), (37547, 1)] : List FactorBlock).map factorBlockValue).prod = 451540223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_859
      · exact prime_quadB_37547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 451540223) ^ 225770111 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 451540223) ^ 64505746 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 451540223) ^ 525658 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 451540223) ^ 12026 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_903080447 : Nat.Prime 903080447 := by
  apply lucas_primality 903080447 (5 : ZMod 903080447)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (451540223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (451540223, 1)] : List FactorBlock).map factorBlockValue).prod = 903080447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_451540223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 903080447) ^ 451540223 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 903080447) ^ 2 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_223963950857 : Nat.Prime 223963950857 := by
  apply lucas_primality 223963950857 (3 : ZMod 223963950857)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (903080447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (903080447, 1)] : List FactorBlock).map factorBlockValue).prod = 223963950857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_31
      · exact prime_quadB_903080447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 223963950857) ^ 111981975428 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 223963950857) ^ 7224643576 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 223963950857) ^ 248 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2170558547748296404399 : Nat.Prime 2170558547748296404399 := by
  apply lucas_primality 2170558547748296404399 (6 : ZMod 2170558547748296404399)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (6299, 1), (12211, 1), (223963950857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (6299, 1), (12211, 1), (223963950857, 1)] : List FactorBlock).map factorBlockValue).prod = 2170558547748296404399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_6299
      · exact prime_quadB_12211
      · exact prime_quadB_223963950857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2170558547748296404399) ^ 1085279273874148202199 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170558547748296404399) ^ 723519515916098801466 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170558547748296404399) ^ 310079792535470914914 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170558547748296404399) ^ 344587799293268202 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170558547748296404399) ^ 177754364732478618 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 2170558547748296404399) ^ 9691553214 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_35279
      · exact prime_quadB_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_61717
      · exact prime_quadB_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_19
      · exact prime_quadB_107
      · exact prime_quadB_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_167470415839663 : Nat.Prime 167470415839663 := by
  apply lucas_primality 167470415839663 (6 : ZMod 167470415839663)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (37, 1), (22807, 1), (2544331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (37, 1), (22807, 1), (2544331, 1)] : List FactorBlock).map factorBlockValue).prod = 167470415839663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_13
      · exact prime_quadB_37
      · exact prime_quadB_22807
      · exact prime_quadB_2544331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 167470415839663) ^ 83735207919831 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 167470415839663) ^ 55823471946554 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 167470415839663) ^ 12882339679974 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 167470415839663) ^ 4526227455126 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 167470415839663) ^ 7342939266 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 167470415839663) ^ 65821002 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3167650329896651990819 : Nat.Prime 3167650329896651990819 := by
  apply lucas_primality 3167650329896651990819 (2 : ZMod 3167650329896651990819)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (257, 1), (751, 1), (167470415839663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (257, 1), (751, 1), (167470415839663, 1)] : List FactorBlock).map factorBlockValue).prod = 3167650329896651990819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_257
      · exact prime_quadB_751
      · exact prime_quadB_167470415839663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3167650329896651990819) ^ 1583825164948325995409 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167650329896651990819) ^ 452521475699521712974 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167650329896651990819) ^ 12325487664967517474 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167650329896651990819) ^ 4217909893337752318 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167650329896651990819) ^ 18914686 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_1123
      · exact prime_quadB_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_67
      · exact prime_quadB_89
      · exact prime_quadB_467
      · exact prime_quadB_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_10238255115841 : Nat.Prime 10238255115841 := by
  apply lucas_primality 10238255115841 (17 : ZMod 10238255115841)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 1), (73, 1), (1361, 1), (11927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 1), (73, 1), (1361, 1), (11927, 1)] : List FactorBlock).map factorBlockValue).prod = 10238255115841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_73
      · exact prime_quadB_1361
      · exact prime_quadB_11927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 10238255115841) ^ 5119127557920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 10238255115841) ^ 3412751705280 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 10238255115841) ^ 2047651023168 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 10238255115841) ^ 140250070080 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 10238255115841) ^ 7522597440 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 10238255115841) ^ 858409920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4675296946232667164981 : Nat.Prime 4675296946232667164981 := by
  apply lucas_primality 4675296946232667164981 (2 : ZMod 4675296946232667164981)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (823, 1), (27743, 1), (10238255115841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (823, 1), (27743, 1), (10238255115841, 1)] : List FactorBlock).map factorBlockValue).prod = 4675296946232667164981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_823
      · exact prime_quadB_27743
      · exact prime_quadB_10238255115841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4675296946232667164981) ^ 2337648473116333582490 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4675296946232667164981) ^ 935059389246533432996 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4675296946232667164981) ^ 5680798233575537260 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4675296946232667164981) ^ 168521679206742860 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4675296946232667164981) ^ 456649780 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_402625124287 : Nat.Prime 402625124287 := by
  apply lucas_primality 402625124287 (6 : ZMod 402625124287)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod = 402625124287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_8761
      · exact prime_quadB_9043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 402625124287) ^ 201312562143 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 134208374762 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 57517874898 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 36602284026 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 45956526 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 44523402 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_9663002982889 : Nat.Prime 9663002982889 := by
  apply lucas_primality 9663002982889 (41 : ZMod 9663002982889)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod = 9663002982889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_402625124287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (41 : ZMod 9663002982889) ^ 4831501491444 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (41 : ZMod 9663002982889) ^ 3221000994296 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (41 : ZMod 9663002982889) ^ 24 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_212586065623559 : Nat.Prime 212586065623559 := by
  apply lucas_primality 212586065623559 (11 : ZMod 212586065623559)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod = 212586065623559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_9663002982889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 212586065623559) ^ 106293032811779 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 212586065623559) ^ 19326005965778 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 212586065623559) ^ 22 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_5893954621823010734653 : Nat.Prime 5893954621823010734653 := by
  apply lucas_primality 5893954621823010734653 (5 : ZMod 5893954621823010734653)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod = 5893954621823010734653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_311
      · exact prime_quadB_212586065623559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5893954621823010734653) ^ 2946977310911505367326 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 1964651540607670244884 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 346703213048412396156 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 310208137990684775508 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 256258896601000466724 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 18951622578209037732 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 27725028 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_7
      · exact prime_quadB_151
      · exact prime_quadB_479
      · exact prime_quadB_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_439
      · exact prime_quadB_853
      · exact prime_quadB_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_29
      · exact prime_quadB_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_244140209 : Nat.Prime 244140209 := by
  apply lucas_primality 244140209 (3 : ZMod 244140209)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod = 244140209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_13
      · exact prime_quadB_37
      · exact prime_quadB_31723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 244140209) ^ 122070104 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 18780016 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 6598384 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 7696 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_5381573389 : Nat.Prime 5381573389 := by
  apply lucas_primality 5381573389 (2 : ZMod 5381573389)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod = 5381573389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_2837
      · exact prime_quadB_158077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5381573389) ^ 2690786694 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1793857796 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1896924 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 34044 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_34890825049700005681357 : Nat.Prime 34890825049700005681357 := by
  apply lucas_primality 34890825049700005681357 (2 : ZMod 34890825049700005681357)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod = 34890825049700005681357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_2213
      · exact prime_quadB_244140209
      · exact prime_quadB_5381573389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34890825049700005681357) ^ 17445412524850002840678 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 11630275016566668560452 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 15766301423271579612 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 142913062918284 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 6483387390204 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_208255577671 : Nat.Prime 208255577671 := by
  apply lucas_primality 208255577671 (7 : ZMod 208255577671)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 2), (107, 1), (109, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 2), (107, 1), (109, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod = 208255577671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_107
      · exact prime_quadB_109
      · exact prime_quadB_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 208255577671) ^ 104127788835 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 69418525890 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 41651115534 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 29750796810 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 1946313810 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 1910601630 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 208255577671) ^ 51433830 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_2499066932053 : Nat.Prime 2499066932053 := by
  apply lucas_primality 2499066932053 (2 : ZMod 2499066932053)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (208255577671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (208255577671, 1)] : List FactorBlock).map factorBlockValue).prod = 2499066932053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_208255577671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2499066932053) ^ 1249533466026 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499066932053) ^ 833022310684 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499066932053) ^ 12 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_129951480466757 : Nat.Prime 129951480466757 := by
  apply lucas_primality 129951480466757 (3 : ZMod 129951480466757)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (2499066932053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (2499066932053, 1)] : List FactorBlock).map factorBlockValue).prod = 129951480466757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_13
      · exact prime_quadB_2499066932053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129951480466757) ^ 64975740233378 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 129951480466757) ^ 9996267728212 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 129951480466757) ^ 52 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_127937752325444133529 : Nat.Prime 127937752325444133529 := by
  apply lucas_primality 127937752325444133529 (11 : ZMod 127937752325444133529)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod = 127937752325444133529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_127
      · exact prime_quadB_129951480466757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127937752325444133529) ^ 63968876162722066764 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 42645917441814711176 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 7525750136790831384 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 6733565911865480712 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 1007383876578300264 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 127937752325444133529) ^ 984504 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_79065530937124474520923 : Nat.Prime 79065530937124474520923 := by
  apply lucas_primality 79065530937124474520923 (2 : ZMod 79065530937124474520923)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod = 79065530937124474520923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_103
      · exact prime_quadB_127937752325444133529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79065530937124474520923) ^ 39532765468562237260461 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 26355176979041491506974 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 767626513952664801174 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 79065530937124474520923) ^ 618 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_103507548020369 : Nat.Prime 103507548020369 := by
  apply lucas_primality 103507548020369 (3 : ZMod 103507548020369)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (1800709, 1), (3592597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (1800709, 1), (3592597, 1)] : List FactorBlock).map factorBlockValue).prod = 103507548020369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_1800709
      · exact prime_quadB_3592597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103507548020369) ^ 51753774010184 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 103507548020369) ^ 57481552 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 103507548020369) ^ 28811344 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_16581001845697167245347 : Nat.Prime 16581001845697167245347 := by
  apply lucas_primality 16581001845697167245347 (2 : ZMod 16581001845697167245347)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (1271359, 1), (103507548020369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (1271359, 1), (103507548020369, 1)] : List FactorBlock).map factorBlockValue).prod = 16581001845697167245347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_7
      · exact prime_quadB_1271359
      · exact prime_quadB_103507548020369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16581001845697167245347) ^ 8290500922848583622673 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581001845697167245347) ^ 5527000615232389081782 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581001845697167245347) ^ 2368714549385309606478 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581001845697167245347) ^ 13041951050566494 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581001845697167245347) ^ 160191234 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_165810018456971672453471 : Nat.Prime 165810018456971672453471 := by
  apply lucas_primality 165810018456971672453471 (7 : ZMod 165810018456971672453471)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (16581001845697167245347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (16581001845697167245347, 1)] : List FactorBlock).map factorBlockValue).prod = 165810018456971672453471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_16581001845697167245347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 165810018456971672453471) ^ 82905009228485836226735 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 165810018456971672453471) ^ 33162003691394334490694 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 165810018456971672453471) ^ 10 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_8861330137459 : Nat.Prime 8861330137459 := by
  apply lucas_primality 8861330137459 (3 : ZMod 8861330137459)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (223, 1), (11503, 1), (575747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (223, 1), (11503, 1), (575747, 1)] : List FactorBlock).map factorBlockValue).prod = 8861330137459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_223
      · exact prime_quadB_11503
      · exact prime_quadB_575747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8861330137459) ^ 4430665068729 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8861330137459) ^ 2953776712486 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8861330137459) ^ 39736906446 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8861330137459) ^ 770349486 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 8861330137459) ^ 15391014 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_431484264271103017339913 : Nat.Prime 431484264271103017339913 := by
  apply lucas_primality 431484264271103017339913 (3 : ZMod 431484264271103017339913)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (3301, 1), (108463, 1), (8861330137459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (3301, 1), (108463, 1), (8861330137459, 1)] : List FactorBlock).map factorBlockValue).prod = 431484264271103017339913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_17
      · exact prime_quadB_3301
      · exact prime_quadB_108463
      · exact prime_quadB_8861330137459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 431484264271103017339913) ^ 215742132135551508669956 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 431484264271103017339913) ^ 25381427310064883372936 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 431484264271103017339913) ^ 130713197295093310312 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 431484264271103017339913) ^ 3978170106590293624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 431484264271103017339913) ^ 48692945368 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1653296428501 : Nat.Prime 1653296428501 := by
  apply lucas_primality 1653296428501 (2 : ZMod 1653296428501)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 3), (19, 2), (157, 1), (19447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 3), (19, 2), (157, 1), (19447, 1)] : List FactorBlock).map factorBlockValue).prod = 1653296428501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_19
      · exact prime_quadB_157
      · exact prime_quadB_19447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1653296428501) ^ 826648214250 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1653296428501) ^ 551098809500 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1653296428501) ^ 330659285700 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1653296428501) ^ 87015601500 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1653296428501) ^ 10530550500 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1653296428501) ^ 85015500 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4407784149736961915989 : Nat.Prime 4407784149736961915989 := by
  apply lucas_primality 4407784149736961915989 (2 : ZMod 4407784149736961915989)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (4337, 1), (4657, 1), (1653296428501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (4337, 1), (4657, 1), (1653296428501, 1)] : List FactorBlock).map factorBlockValue).prod = 4407784149736961915989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_11
      · exact prime_quadB_4337
      · exact prime_quadB_4657
      · exact prime_quadB_1653296428501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4407784149736961915989) ^ 2203892074868480957994 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407784149736961915989) ^ 1469261383245653971996 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407784149736961915989) ^ 400707649976087446908 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407784149736961915989) ^ 1016320993713848724 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407784149736961915989) ^ 946485752573966484 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407784149736961915989) ^ 2666057988 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_573011939465805049078571 : Nat.Prime 573011939465805049078571 := by
  apply lucas_primality 573011939465805049078571 (2 : ZMod 573011939465805049078571)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (4407784149736961915989, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (4407784149736961915989, 1)] : List FactorBlock).map factorBlockValue).prod = 573011939465805049078571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_13
      · exact prime_quadB_4407784149736961915989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 573011939465805049078571) ^ 286505969732902524539285 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 573011939465805049078571) ^ 114602387893161009815714 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 573011939465805049078571) ^ 44077841497369619159890 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 573011939465805049078571) ^ 130 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_61
      · exact prime_quadB_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_3061
      · exact prime_quadB_61379
      · exact prime_quadB_382747
      · exact prime_quadB_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_315283291 : Nat.Prime 315283291 := by
  apply lucas_primality 315283291 (7 : ZMod 315283291)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod = 315283291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_37
      · exact prime_quadB_40577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315283291) ^ 157641645 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 105094430 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 63056658 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 45040470 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 8521170 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 7770 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_18054505621 : Nat.Prime 18054505621 := by
  apply lucas_primality 18054505621 (2 : ZMod 18054505621)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod = 18054505621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_751
      · exact prime_quadB_133559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18054505621) ^ 9027252810 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 6018168540 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 3610901124 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 24040620 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 135180 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_58528063569446646906503 : Nat.Prime 58528063569446646906503 := by
  apply lucas_primality 58528063569446646906503 (5 : ZMod 58528063569446646906503)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod = 58528063569446646906503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_53
      · exact prime_quadB_97
      · exact prime_quadB_315283291
      · exact prime_quadB_18054505621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58528063569446646906503) ^ 29264031784723323453251 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 1104303086215974469934 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 603382098654089143366 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 185636426795122 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 3241742798062 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1170561271388932938130061 : Nat.Prime 1170561271388932938130061 := by
  apply lucas_primality 1170561271388932938130061 (2 : ZMod 1170561271388932938130061)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod = 1170561271388932938130061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_58528063569446646906503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1170561271388932938130061) ^ 585280635694466469065030 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 234112254277786587626012 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 20 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_31
      · exact prime_quadB_59
      · exact prime_quadB_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_31
      · exact prime_quadB_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_1321
      · exact prime_quadB_1255074433
      · exact prime_quadB_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_176151247 : Nat.Prime 176151247 := by
  apply lucas_primality 176151247 (5 : ZMod 176151247)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (131, 1), (13183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (131, 1), (13183, 1)] : List FactorBlock).map factorBlockValue).prod = 176151247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_17
      · exact prime_quadB_131
      · exact prime_quadB_13183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 176151247) ^ 88075623 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 176151247) ^ 58717082 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 176151247) ^ 10361838 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 176151247) ^ 1344666 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (5 : ZMod 176151247) ^ 13362 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_3092915327934132812325341 : Nat.Prime 3092915327934132812325341 := by
  apply lucas_primality 3092915327934132812325341 (3 : ZMod 3092915327934132812325341)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (331, 1), (947, 1), (1429, 1), (279991, 1), (176151247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (331, 1), (947, 1), (1429, 1), (279991, 1), (176151247, 1)] : List FactorBlock).map factorBlockValue).prod = 3092915327934132812325341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_331
      · exact prime_quadB_947
      · exact prime_quadB_1429
      · exact prime_quadB_279991
      · exact prime_quadB_176151247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3092915327934132812325341) ^ 1546457663967066406162670 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 618583065586826562465068 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 441845046847733258903620 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 9344155069287410309140 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 3266014073848081111220 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 2164391412130253892460 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 11046481236661652740 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092915327934132812325341) ^ 17558293685733220 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_60629070979631911154428801 : Nat.Prime 60629070979631911154428801 := by
  apply lucas_primality 60629070979631911154428801 (101 : ZMod 60629070979631911154428801)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 60629070979631911154428801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 60629070979631911154428801) ^ 30314535489815955577214400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 20209690326543970384809600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 12125814195926382230885760 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 8661295854233130164918400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 5511733725421082832220800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 3566415939978347714966400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 3191003735770100587075200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 2636046564331822224105600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 2090657619987307281187200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1955776483213932617884800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1638623539990051652822400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1478757828771510028156800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1409978394875160724521600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1289980233609189599030400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1143944735464753040649600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 1027611372536134087363200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 60629070979631911154428801) ^ 993919196387408379580800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_61416461511834922987603201 : Nat.Prime 61416461511834922987603201 := by
  apply lucas_primality 61416461511834922987603201 (89 : ZMod 61416461511834922987603201)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 3), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 3), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 61416461511834922987603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 61416461511834922987603201) ^ 30708230755917461493801600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 20472153837278307662534400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 12283292302366984597520640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 8773780215976417569657600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 4724343193218070999046400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 3612733030107936646329600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 3232445342728153841452800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 2670280935297170564678400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 2117809017649480103020800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1981176177801126547987200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1659904365184727648313600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1497962475898412755795200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1428289802600812162502400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1306733223656062191225600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1158801160600658924294400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1040956974776863101484800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (89 : ZMod 61416461511834922987603201) ^ 1006827237898933163731200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_63906318059612014460073601 : Nat.Prime 63906318059612014460073601 := by
  apply lucas_primality 63906318059612014460073601 (67 : ZMod 63906318059612014460073601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 63906318059612014460073601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 63906318059612014460073601) ^ 31953159029806007230036800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 21302106019870671486691200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 12781263611922402892014720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 9129474008516002065724800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 5809665278146546769097600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 4915870619970154958467200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 3759195179977177321180800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 3363490424190106024214400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 2778535567809218020003200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 2203666139986621188278400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 2061494130955226272905600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1558690684380780840489600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1486193443246791033955200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1359708894885362009788800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1205779586030415367171200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1083157933213762956950400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 63906318059612014460073601) ^ 1047644558354295319017600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_67558107663018415286363521 : Nat.Prime 67558107663018415286363521 := by
  apply lucas_primality 67558107663018415286363521 (73 : ZMod 67558107663018415286363521)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 67558107663018415286363521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 67558107663018415286363521) ^ 33779053831509207643181760 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 22519369221006138428787840 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 13511621532603683057272704 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 9651158237574059326623360 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 6141646151183492298760320 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 5196777512539878098951040 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 3974006333118730310962560 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 3555689877000969225598080 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 2937309028826887621146240 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 2329589919414428113322880 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 2179293795581239202785920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1825894801703200413144960 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1647758723488254031374720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1571118782860893378752640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1437406546021668410348160 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1274681276660724816723840 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1145052672254549411633280 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (73 : ZMod 67558107663018415286363521) ^ 1107509961688826480104320 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_69545110829577780441844801 : Nat.Prime 69545110829577780441844801 := by
  apply lucas_primality 69545110829577780441844801 (17 : ZMod 69545110829577780441844801)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 69545110829577780441844801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 69545110829577780441844801) ^ 34772555414788890220922400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 23181703609859260147281600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 13909022165915556088368960 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 9935015832796825777406400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 6322282802688889131076800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 5349623909967521572449600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 3660268991030409496939200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 3023700470851207845297600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 2398107269985440704891200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 2243390671921863885220800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1879597589988588660590400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1696222215355555620532800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1617328158827390242833600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1479683209139952775358400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1312171902444863781921600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1178730692026742041387200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (17 : ZMod 69545110829577780441844801) ^ 1140083784091439023636800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_96511582375740593266233601 : Nat.Prime 96511582375740593266233601 := by
  apply lucas_primality 96511582375740593266233601 (7 : ZMod 96511582375740593266233601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 96511582375740593266233601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 96511582375740593266233601) ^ 48255791187870296633116800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 32170527458580197755411200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 19302316475148118653246720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 8773780215976417569657600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 7423967875056968712787200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 5677151904455329015660800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 5079556967144241750854400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 4196155755466982315923200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 3327985599163468733318400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 3113276850830341718265600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 2608421145290286304492800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 2353941033554648616249600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 2244455404086990541075200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 2053437922888097729068800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 1820973252372464023891200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 1635789531792213445190400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 96511582375740593266233601) ^ 1582157088126894971577600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_105090389698028646001009921 : Nat.Prime 105090389698028646001009921 := by
  apply lucas_primality 105090389698028646001009921 (113 : ZMod 105090389698028646001009921)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 105090389698028646001009921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 105090389698028646001009921) ^ 52545194849014323000504960 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 35030129899342882000336640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 21018077939605729200201984 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 15012912814004092285858560 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 9553671790729876909182720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 8083876130617588153923840 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 6181787629295802705941760 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 5531073142001507684263680 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 4569147378175158521783040 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 3623806541311332620724480 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 3390012570904149871000320 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 2840280802649422864892160 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 2563180236537284048805120 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 2443962551116945255837440 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 2235965738255928638319360 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 1982837541472238603792640 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 1781193045729299084762880 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 105090389698028646001009921) ^ 1722793273738174524606720 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_107478807645711115228305601 : Nat.Prime 107478807645711115228305601 := by
  apply lucas_primality 107478807645711115228305601 (67 : ZMod 107478807645711115228305601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 107478807645711115228305601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 107478807645711115228305601) ^ 53739403822855557614152800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 35826269215237038409435200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 21495761529142223045661120 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 15354115377958730746900800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 8267600588131624248331200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 6322282802688889131076800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 5656779349774269222542400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 4672991636770048488187200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3706165780886590180286400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3467058311151971458977600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2904832639073273384548800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2621434332822222322641600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2499507154551421284379200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2286783141398108834644800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2027902031051153117515200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1821674705859510427598400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1761947666323133036529600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_121258141959263822308857601 : Nat.Prime 121258141959263822308857601 := by
  apply lucas_primality 121258141959263822308857601 (65 : ZMod 121258141959263822308857601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 121258141959263822308857601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (65 : ZMod 121258141959263822308857601) ^ 60629070979631911154428800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 40419380653087940769619200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 24251628391852764461771520 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 17322591708466260329836800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 11023467450842165664441600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 7132831879956695429932800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 6382007471540201174150400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 5272093128663644448211200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 4181315239974614562374400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 3911552966427865235769600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 3277247079980103305644800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 2957515657543020056313600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 2819956789750321449043200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 2579960467218379198060800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 2287889470929506081299200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 2055222745072268174726400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (65 : ZMod 121258141959263822308857601) ^ 1987838392774816759161600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_131362987122535807501262401 : Nat.Prime 131362987122535807501262401 := by
  apply lucas_primality 131362987122535807501262401 (71 : ZMod 131362987122535807501262401)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 131362987122535807501262401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 131362987122535807501262401) ^ 65681493561267903750631200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 43787662374178602500420800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 26272597424507161500252480 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 18766141017505115357323200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 11942089738412346136478400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 10104845163271985192404800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 7727234536619753382427200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 6913841427501884605329600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 5711434222718948152228800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4529758176639165775905600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4237515713630187338750400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3550351003311778581115200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3203975295671605061006400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3054953188896181569796800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2794957172819910797899200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2478546926840298254740800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2226491307161623855953600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2153491592172718155758400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_152550565690686744195014401 : Nat.Prime 152550565690686744195014401 := by
  apply lucas_primality 152550565690686744195014401 (113 : ZMod 152550565690686744195014401)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 152550565690686744195014401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 152550565690686744195014401) ^ 76275282845343372097507200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 50850188563562248065004800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 30510113138137348839002880 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 21792937955812392027859200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 13868233244607885835910400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 11734658899283595707308800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 8973562687687455540883200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 8028977141615091799737600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 6632633290899423660652800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 5260364334161611868793600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 4122988261910452545811200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3720745504650896199878400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3547687574202017306860800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3245756716823122216915200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2878312560201636682924800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2585602808316724477881600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2500828945748963019590400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_214957615291422230456611201 : Nat.Prime 214957615291422230456611201 := by
  apply lucas_primality 214957615291422230456611201 (11 : ZMod 214957615291422230456611201)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 214957615291422230456611201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 214957615291422230456611201) ^ 107478807645711115228305600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 71652538430474076818870400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 42991523058284446091322240 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 30708230755917461493801600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 16535201176263248496662400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 12644565605377778262153600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 11313558699548538445084800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 9345983273540096976374400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 7412331561773180360572800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 6934116622303942917955200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5809665278146546769097600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5242868665644444645283200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4999014309102842568758400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4573566282796217669289600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4055804062102306235030400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3643349411719020855196800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3523895332646266073059200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_33677401 : Nat.Prime 33677401 := by
  apply lucas_primality 33677401 (11 : ZMod 33677401)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (37, 2), (41, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (37, 2), (41, 1)] : List FactorBlock).map factorBlockValue).prod = 33677401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_37
      · exact prime_quadB_41
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33677401) ^ 16838700 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 11225800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 6735480 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 910200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 821400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_196577599972351511 : Nat.Prime 196577599972351511 := by
  apply lucas_primality 196577599972351511 (7 : ZMod 196577599972351511)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 2), (4824031, 1), (33677401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 2), (4824031, 1), (33677401, 1)] : List FactorBlock).map factorBlockValue).prod = 196577599972351511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_5
      · exact prime_quadB_11
      · exact prime_quadB_4824031
      · exact prime_quadB_33677401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 196577599972351511) ^ 98288799986175755 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 39315519994470302 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 17870690906577410 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 40749655210 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 5837077510 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1957395503481493820383049 : Nat.Prime 1957395503481493820383049 := by
  apply lucas_primality 1957395503481493820383049 (3 : ZMod 1957395503481493820383049)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (109, 1), (601, 1), (196577599972351511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (109, 1), (601, 1), (196577599972351511, 1)] : List FactorBlock).map factorBlockValue).prod = 1957395503481493820383049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_19
      · exact prime_quadB_109
      · exact prime_quadB_601
      · exact prime_quadB_196577599972351511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1957395503481493820383049) ^ 978697751740746910191524 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 103020815972710201072792 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 17957756912674255232872 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 3256897676341919834248 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 9957368 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_591133442051411133755680799 : Nat.Prime 591133442051411133755680799 := by
  apply lucas_primality 591133442051411133755680799 (67 : ZMod 591133442051411133755680799)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (151, 1), (1957395503481493820383049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (151, 1), (1957395503481493820383049, 1)] : List FactorBlock).map factorBlockValue).prod = 591133442051411133755680799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_151
      · exact prime_quadB_1957395503481493820383049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (67 : ZMod 591133442051411133755680799) ^ 295566721025705566877840399 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 591133442051411133755680799) ^ 3914791006962987640766098 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 591133442051411133755680799) ^ 302 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_945813507282257814009089279 : Nat.Prime 945813507282257814009089279 := by
  apply lucas_primality 945813507282257814009089279 (67 : ZMod 945813507282257814009089279)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (878131, 1), (538537819119389825669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (878131, 1), (538537819119389825669, 1)] : List FactorBlock).map factorBlockValue).prod = 945813507282257814009089279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_878131
      · exact prime_quadB_538537819119389825669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (67 : ZMod 945813507282257814009089279) ^ 472906753641128907004544639 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 945813507282257814009089279) ^ 1077075638238779651338 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (67 : ZMod 945813507282257814009089279) ^ 1756262 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_5
      · exact prime_quadB_7
      · exact prime_quadB_11
      · exact prime_quadB_13
      · exact prime_quadB_17
      · exact prime_quadB_19
      · exact prime_quadB_23
      · exact prime_quadB_29
      · exact prime_quadB_31
      · exact prime_quadB_37
      · exact prime_quadB_41
      · exact prime_quadB_43
      · exact prime_quadB_47
      · exact prime_quadB_53
      · exact prime_quadB_59
      · exact prime_quadB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem prime_quadB_4729067536411289070045446473 : Nat.Prime 4729067536411289070045446473 := by
  apply lucas_primality 4729067536411289070045446473 (7 : ZMod 4729067536411289070045446473)
  · rw [← quadFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod = 4729067536411289070045446473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_quadB_2
      · exact prime_quadB_3
      · exact prime_quadB_1051
      · exact prime_quadB_1153
      · exact prime_quadB_940369
      · exact prime_quadB_6947861
      · exact prime_quadB_8295863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4729067536411289070045446473) ^ 2364533768205644535022723236 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 1576355845470429690015148824 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 4499588521799513863030872 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 4101532989081777163959624 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 5028948781181949926088 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 680650855912530355752 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide
    · change (7 : ZMod 4729067536411289070045446473) ^ 570051305863089719544 ≠ 1
      rw [← quadFastPow_eq_pow]
      decide

private theorem phi_quadB_4729067536411289070045446385 : Nat.totient 4729067536411289070045446385 = 2507128579225134972080640000 := by
  rw [← show ((([(3, 1), (5, 1), (241, 1), (587, 1), (8461, 1), (23413451, 1), (11249727107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446385 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_5, prime_quadB_241, prime_quadB_587, prime_quadB_8461, prime_quadB_23413451, prime_quadB_11249727107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446386 : Nat.totient 4729067536411289070045446386 = 2020849414959044717617489920 := by
  rw [← show ((([(2, 1), (7, 1), (347, 1), (72689, 1), (80021, 1), (167357560715593, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446386 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_7, prime_quadB_347, prime_quadB_72689, prime_quadB_80021, prime_quadB_167357560715593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446387 : Nat.totient 4729067536411289070045446387 = 4365293110525884184002284832 := by
  rw [← show ((([(13, 1), (573887395997, 1), (633877705653067, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446387 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_13, prime_quadB_573887395997, prime_quadB_633877705653067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446388 : Nat.totient 4729067536411289070045446388 = 1576308373290739859152784224 := by
  rw [← show ((([(2, 2), (3, 1), (33347, 1), (7846799, 1), (1506069358139483, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446388 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_33347, prime_quadB_7846799, prime_quadB_1506069358139483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446389 : Nat.totient 4729067536411289070045446389 = 4268223152549103281008969200 := by
  rw [← show ((([(11, 1), (139, 1), (3092915327934132812325341, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446389 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_11, prime_quadB_139, prime_quadB_3092915327934132812325341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446390 : Nat.totient 4729067536411289070045446390 = 1891624860413239150455363360 := by
  rw [← show ((([(2, 1), (5, 1), (878131, 1), (538537819119389825669, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446390 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_878131, prime_quadB_538537819119389825669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446391 : Nat.totient 4729067536411289070045446391 = 3151716830830117549995557760 := by
  rw [← show ((([(3, 2), (3169, 1), (165810018456971672453471, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446391 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_3169, prime_quadB_165810018456971672453471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446392 : Nat.totient 4729067536411289070045446392 = 2364533768205644535022723192 := by
  rw [← show ((([(2, 3), (591133442051411133755680799, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446392 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_591133442051411133755680799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446393 : Nat.totient 4729067536411289070045446393 = 4053486351584156831643551184 := by
  rw [← show ((([(7, 1), (37463963, 1), (18032824680885579373, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446393 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_7, prime_quadB_37463963, prime_quadB_18032824680885579373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446394 : Nat.totient 4729067536411289070045446394 = 1576349510169769896710669520 := by
  rw [← show ((([(2, 1), (3, 1), (248821, 1), (3167650329896651990819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446394 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_248821, prime_quadB_3167650329896651990819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446395 : Nat.totient 4729067536411289070045446395 = 3783254029129031256036357112 := by
  rw [← show ((([(5, 1), (945813507282257814009089279, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446395 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_945813507282257814009089279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446396 : Nat.totient 4729067536411289070045446396 = 2345914417695629553539117568 := by
  rw [← show ((([(2, 2), (127, 1), (4597709, 1), (5054317, 1), (400597142329, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446396 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_127, prime_quadB_4597709, prime_quadB_5054317, prime_quadB_400597142329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446397 : Nat.totient 4729067536411289070045446397 = 3133825907520671847475622400 := by
  rw [← show ((([(3, 1), (167, 1), (443941, 1), (14839757, 1), (1432800567881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446397 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_167, prime_quadB_443941, prime_quadB_14839757, prime_quadB_1432800567881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446398 : Nat.totient 4729067536411289070045446398 = 2362709121830636037160524480 := by
  rw [← show ((([(2, 1), (1531, 1), (11923, 1), (28807, 1), (4496625855541289, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446398 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_1531, prime_quadB_11923, prime_quadB_28807, prime_quadB_4496625855541289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446399 : Nat.totient 4729067536411289070045446399 = 4728768843324818344589293056 := by
  rw [← show ((([(18713, 1), (109469, 1), (1701179, 1), (1357034643673, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446399 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_18713, prime_quadB_109469, prime_quadB_1701179, prime_quadB_1357034643673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446400 : Nat.totient 4729067536411289070045446400 = 622285473837442557542400000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_5, prime_quadB_7, prime_quadB_11, prime_quadB_13, prime_quadB_17, prime_quadB_19, prime_quadB_23, prime_quadB_29, prime_quadB_31, prime_quadB_37, prime_quadB_41, prime_quadB_43, prime_quadB_47, prime_quadB_53, prime_quadB_59, prime_quadB_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446401 : Nat.totient 4729067536411289070045446401 = 4716759632945508174057984000 := by
  rw [← show ((([(401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_401, prime_quadB_11069, prime_quadB_53269, prime_quadB_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446402 : Nat.totient 4729067536411289070045446402 = 2364522518859718621007607552 := by
  rw [← show ((([(2, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_210193, prime_quadB_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446403 : Nat.totient 4729067536411289070045446403 = 3152711690940859380030297600 := by
  rw [← show ((([(3, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446404 : Nat.totient 4729067536411289070045446404 = 2341109655706591279001952384 := by
  rw [← show ((([(2, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_103, prime_quadB_5009, prime_quadB_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446405 : Nat.totient 4729067536411289070045446405 = 3744196689785619569559904000 := by
  rw [← show ((([(5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_107, prime_quadB_1013, prime_quadB_144417341, prime_quadB_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446406 : Nat.totient 4729067536411289070045446406 = 1571549729260898912144256000 := by
  rw [← show ((([(2, 1), (3, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_421, prime_quadB_1483, prime_quadB_2072201, prime_quadB_2567179, prime_quadB_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446407 : Nat.totient 4729067536411289070045446407 = 4049757401400441527193596952 := by
  rw [← show ((([(7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_7, prime_quadB_1087, prime_quadB_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446408 : Nat.totient 4729067536411289070045446408 = 2364533766271648981528824400 := by
  rw [← show ((([(2, 3), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_1222615931, prime_quadB_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446409 : Nat.totient 4729067536411289070045446409 = 3152711690940859380030297600 := by
  rw [← show ((([(3, 2), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446410 : Nat.totient 4729067536411289070045446410 = 1883275367375349618397538112 := by
  rw [← show ((([(2, 1), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_239, prime_quadB_4327, prime_quadB_1214459, prime_quadB_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446411 : Nat.totient 4729067536411289070045446411 = 4298380879342397520174606720 := by
  rw [← show ((([(11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_11, prime_quadB_5573, prime_quadB_3198253273, prime_quadB_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446412 : Nat.totient 4729067536411289070045446412 = 1576355845470429690015148800 := by
  rw [← show ((([(2, 2), (3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446413 : Nat.totient 4729067536411289070045446413 = 4347901504515435859680150000 := by
  rw [← show ((([(13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_13, prime_quadB_251, prime_quadB_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446414 : Nat.totient 4729067536411289070045446414 = 2026722447682971779648341752 := by
  rw [← show ((([(2, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_7, prime_quadB_97523, prime_quadB_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446415 : Nat.totient 4729067536411289070045446415 = 2522022553179878183696046720 := by
  rw [← show ((([(3, 1), (5, 1), (22397, 1), (73771, 1), (190813341386997503, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_5, prime_quadB_22397, prime_quadB_73771, prime_quadB_190813341386997503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446416 : Nat.totient 4729067536411289070045446416 = 2364533655236198298650382336 := by
  rw [← show ((([(2, 4), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_20930737, prime_quadB_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446417 : Nat.totient 4729067536411289070045446417 = 4387034880091442101345320960 := by
  rw [← show ((([(17, 1), (73, 1), (1609, 1), (29021, 1), (2685877, 1), (30384297329, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_17, prime_quadB_73, prime_quadB_1609, prime_quadB_29021, prime_quadB_2685877, prime_quadB_30384297329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446418 : Nat.totient 4729067536411289070045446418 = 1548204829647044226382771200 := by
  rw [← show ((([(2, 1), (3, 2), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_67, prime_quadB_491, prime_quadB_1061, prime_quadB_9492089, prime_quadB_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446419 : Nat.totient 4729067536411289070045446419 = 4470467654769242318905337856 := by
  rw [← show ((([(19, 1), (463, 1), (177409, 1), (3030158014634483503, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_19, prime_quadB_463, prime_quadB_177409, prime_quadB_3030158014634483503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446420 : Nat.totient 4729067536411289070045446420 = 1891627011543136663647837216 := by
  rw [← show ((([(2, 2), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_626080687, prime_quadB_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446421 : Nat.totient 4729067536411289070045446421 = 2702324306512326689345606448 := by
  rw [← show ((([(3, 1), (7, 1), (321473185079, 1), (700505369226119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_7, prime_quadB_321473185079, prime_quadB_700505369226119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446422 : Nat.totient 4729067536411289070045446422 = 2149576152914222304566112000 := by
  rw [← show ((([(2, 1), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_11, prime_quadB_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446423 : Nat.totient 4729067536411289070045446423 = 4406013387276116717441635680 := by
  rw [← show ((([(23, 1), (71, 1), (83, 1), (34890825049700005681357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_23, prime_quadB_71, prime_quadB_83, prime_quadB_34890825049700005681357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446424 : Nat.totient 4729067536411289070045446424 = 1572466828560993711443107584 := by
  rw [← show ((([(2, 3), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_409, prime_quadB_45127, prime_quadB_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446425 : Nat.totient 4729067536411289070045446425 = 3783253996622399876788598720 := by
  rw [← show ((([(5, 2), (116384069, 1), (1625331568846003853, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_116384069, prime_quadB_1625331568846003853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446426 : Nat.totient 4729067536411289070045446426 = 2182646555266243577460304944 := by
  rw [← show ((([(2, 1), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_13, prime_quadB_4887540332063, prime_quadB_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446427 : Nat.totient 4729067536411289070045446427 = 3152605599757666565836538976 := by
  rw [← show ((([(3, 3), (29717, 1), (5893954621823010734653, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_29717, prime_quadB_5893954621823010734653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446428 : Nat.totient 4729067536411289070045446428 = 2022346823602002270213839040 := by
  rw [← show ((([(2, 2), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_7, prime_quadB_461, prime_quadB_13492702567, prime_quadB_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446429 : Nat.totient 4729067536411289070045446429 = 4565995948142389138240307200 := by
  rw [← show ((([(29, 1), (15535361, 1), (10496781784408483841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_29, prime_quadB_15535361, prime_quadB_10496781784408483841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446430 : Nat.totient 4729067536411289070045446430 = 1261082653069483780238868512 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_5, prime_quadB_623279, prime_quadB_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446431 : Nat.totient 4729067536411289070045446431 = 4576516970720602325850432000 := by
  rw [← show ((([(31, 1), (152550565690686744195014401, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_31, prime_quadB_152550565690686744195014401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446432 : Nat.totient 4729067536411289070045446432 = 2352154001917303943676602880 := by
  rw [← show ((([(2, 5), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_191, prime_quadB_282045737, prime_quadB_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446433 : Nat.totient 4729067536411289070045446433 = 2844237220717778503188480000 := by
  rw [← show ((([(3, 1), (11, 1), (293, 1), (313, 1), (1249, 1), (4201, 1), (297806723575661, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_11, prime_quadB_293, prime_quadB_313, prime_quadB_1249, prime_quadB_4201, prime_quadB_297806723575661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446434 : Nat.totient 4729067536411289070045446434 = 2213650503512042666304430080 := by
  rw [← show ((([(2, 1), (17, 1), (229, 1), (1669, 1), (2963, 1), (108608761, 1), (1130858507, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_17, prime_quadB_229, prime_quadB_1669, prime_quadB_2963, prime_quadB_108608761, prime_quadB_1130858507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446435 : Nat.totient 4729067536411289070045446435 = 3242758483711376322453171168 := by
  rw [← show ((([(5, 1), (7, 1), (105683, 1), (1278504729483803739227, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_7, prime_quadB_105683, prime_quadB_1278504729483803739227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446436 : Nat.totient 4729067536411289070045446436 = 1576355845470429690015148800 := by
  rw [← show ((([(2, 2), (3, 2), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446437 : Nat.totient 4729067536411289070045446437 = 4584628896777536124127345920 := by
  rw [← show ((([(37, 1), (277, 1), (310627, 1), (21263909, 1), (69857287091, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_37, prime_quadB_277, prime_quadB_310627, prime_quadB_21263909, prime_quadB_69857287091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446438 : Nat.totient 4729067536411289070045446438 = 2215720412886444789464064000 := by
  rw [← show ((([(2, 1), (19, 1), (149, 1), (349, 1), (1213, 1), (2897, 1), (6151, 1), (110719776691, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_19, prime_quadB_149, prime_quadB_349, prime_quadB_1213, prime_quadB_2897, prime_quadB_6151, prime_quadB_110719776691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446439 : Nat.totient 4729067536411289070045446439 = 2910195407022331735412582400 := by
  rw [← show ((([(3, 1), (13, 1), (121258141959263822308857601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_13, prime_quadB_121258141959263822308857601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446440 : Nat.totient 4729067536411289070045446440 = 1872898034222292701008096000 := by
  rw [← show ((([(2, 3), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_101, prime_quadB_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446441 : Nat.totient 4729067536411289070045446441 = 4544255915426801429728604160 := by
  rw [← show ((([(41, 1), (89, 1), (263, 1), (16823, 1), (344213, 1), (850971844357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_41, prime_quadB_89, prime_quadB_263, prime_quadB_16823, prime_quadB_344213, prime_quadB_850971844357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446442 : Nat.totient 4729067536411289070045446442 = 1350749207586578901940666368 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (4787, 1), (10337, 1), (269456833, 1), (8444599963, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_7, prime_quadB_4787, prime_quadB_10337, prime_quadB_269456833, prime_quadB_8444599963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446443 : Nat.totient 4729067536411289070045446443 = 4560618365248178465243889696 := by
  rw [← show ((([(43, 1), (79, 1), (3322747, 1), (418969776239939677, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_43, prime_quadB_79, prime_quadB_3322747, prime_quadB_418969776239939677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446444 : Nat.totient 4729067536411289070045446444 = 2149576152914222304566112000 := by
  rw [← show ((([(2, 2), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_11, prime_quadB_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446445 : Nat.totient 4729067536411289070045446445 = 2522169352752687504024238080 := by
  rw [← show ((([(3, 2), (5, 1), (105090389698028646001009921, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_5, prime_quadB_105090389698028646001009921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446446 : Nat.totient 4729067536411289070045446446 = 2260548953839384818190783488 := by
  rw [← show ((([(2, 1), (23, 1), (2417, 1), (9343, 1), (1789993, 1), (2543333740247, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_23, prime_quadB_2417, prime_quadB_9343, prime_quadB_1789993, prime_quadB_2543333740247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446447 : Nat.totient 4729067536411289070045446447 = 4615196897792127895633921536 := by
  rw [← show ((([(47, 1), (757, 1), (823, 1), (3037, 1), (3351109, 1), (15868964827, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_47, prime_quadB_757, prime_quadB_823, prime_quadB_3037, prime_quadB_3351109, prime_quadB_15868964827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446448 : Nat.totient 4729067536411289070045446448 = 1571285768495580038334904320 := by
  rw [← show ((([(2, 4), (3, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_311, prime_quadB_1115447, prime_quadB_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446449 : Nat.totient 4729067536411289070045446449 = 4053486459781104917181811200 := by
  rw [← show ((([(7, 2), (96511582375740593266233601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_7, prime_quadB_96511582375740593266233601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446450 : Nat.totient 4729067536411289070045446450 = 1889718170330302521809688000 := by
  rw [← show ((([(2, 1), (5, 2), (991, 1), (49777621, 1), (1917333766315939, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_991, prime_quadB_49777621, prime_quadB_1917333766315939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446451 : Nat.totient 4729067536411289070045446451 = 2967258062061249671351689344 := by
  rw [← show ((([(3, 1), (17, 1), (5218085973487, 1), (17770273412623, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_17, prime_quadB_5218085973487, prime_quadB_17770273412623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446452 : Nat.totient 4729067536411289070045446452 = 2182644900860521172980664448 := by
  rw [← show ((([(2, 2), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_13, prime_quadB_1319293, prime_quadB_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446453 : Nat.totient 4729067536411289070045446453 = 4639106738981933476761624576 := by
  rw [← show ((([(53, 1), (6329, 1), (28653985897, 1), (492016319777, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_53, prime_quadB_6329, prime_quadB_28653985897, prime_quadB_492016319777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446454 : Nat.totient 4729067536411289070045446454 = 1575791914973298118263498240 := by
  rw [← show ((([(2, 1), (3, 4), (3511, 1), (13709, 1), (606490351024352033, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_3511, prime_quadB_13709, prime_quadB_606490351024352033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446455 : Nat.totient 4729067536411289070045446455 = 3434054883899790380515968000 := by
  rw [← show ((([(5, 1), (11, 1), (653, 1), (634614601, 1), (207486376117277, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_11, prime_quadB_653, prime_quadB_634614601, prime_quadB_207486376117277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446456 : Nat.totient 4729067536411289070045446456 = 2019318916409645727744000000 := by
  rw [← show ((([(2, 3), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_7, prime_quadB_433, prime_quadB_751, prime_quadB_39551, prime_quadB_40376737, prime_quadB_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446457 : Nat.totient 4729067536411289070045446457 = 2970086110711840484884340352 := by
  rw [← show ((([(3, 1), (19, 1), (179, 1), (397763, 1), (1165261096003739113, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_19, prime_quadB_179, prime_quadB_397763, prime_quadB_1165261096003739113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446458 : Nat.totient 4729067536411289070045446458 = 2280407113088797134610022400 := by
  rw [← show ((([(2, 1), (29, 1), (1229, 1), (3121, 1), (911749, 1), (23314525201361, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_29, prime_quadB_1229, prime_quadB_3121, prime_quadB_911749, prime_quadB_23314525201361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446459 : Nat.totient 4729067536411289070045446459 = 4646243594311223746272430080 := by
  rw [← show ((([(59, 1), (1741, 1), (47337677249, 1), (972563102789, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_59, prime_quadB_1741, prime_quadB_47337677249, prime_quadB_972563102789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446460 : Nat.totient 4729067536411289070045446460 = 1261084436171706118228022592 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_5, prime_quadB_5250043, prime_quadB_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446461 : Nat.totient 4729067536411289070045446461 = 4651541839092003807504042240 := by
  rw [← show ((([(61, 1), (7631487426569, 1), (10158661475129, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_61, prime_quadB_7631487426569, prime_quadB_10158661475129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446462 : Nat.totient 4729067536411289070045446462 = 2288248379168577413923676160 := by
  rw [← show ((([(2, 1), (31, 1), (241513, 1), (3623449, 1), (87160790647873, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_31, prime_quadB_241513, prime_quadB_3623449, prime_quadB_87160790647873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446463 : Nat.totient 4729067536411289070045446463 = 2681695876699967629687707600 := by
  rw [← show ((([(3, 2), (7, 1), (131, 1), (573011939465805049078571, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_7, prime_quadB_131, prime_quadB_573011939465805049078571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446464 : Nat.totient 4729067536411289070045446464 = 2364533768193799604402617344 := by
  rw [← show ((([(2, 6), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_199731886537, prime_quadB_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446465 : Nat.totient 4729067536411289070045446465 = 3491455488031207798676637696 := by
  rw [← show ((([(5, 1), (13, 1), (4483, 1), (644537483, 1), (25179392167649, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_5, prime_quadB_13, prime_quadB_4483, prime_quadB_644537483, prime_quadB_25179392167649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446466 : Nat.totient 4729067536411289070045446466 = 1433050768347588254158216640 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (5471890517, 1), (13094658639069053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_11, prime_quadB_5471890517, prime_quadB_13094658639069053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446467 : Nat.totient 4729067536411289070045446467 = 4729065365852741321746863336 := by
  rw [← show ((([(2178733, 1), (2170558547748296404399, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2178733, prime_quadB_2170558547748296404399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446468 : Nat.totient 4729067536411289070045446468 = 2225443546546488974139033600 := by
  rw [← show ((([(2, 2), (17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_17, prime_quadB_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446469 : Nat.totient 4729067536411289070045446469 = 3015635775216666803774491248 := by
  rw [← show ((([(3, 1), (23, 1), (2017987, 1), (33963157677738943723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_23, prime_quadB_2017987, prime_quadB_33963157677738943723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446470 : Nat.totient 4729067536411289070045446470 = 1621394583912441966872724480 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (67558107663018415286363521, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_7, prime_quadB_67558107663018415286363521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446471 : Nat.totient 4729067536411289070045446471 = 4728789208490871251249302080 := by
  rw [← show ((([(21587, 1), (79811, 1), (820766489, 1), (3344266327, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_21587, prime_quadB_79811, prime_quadB_820766489, prime_quadB_3344266327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446472 : Nat.totient 4729067536411289070045446472 = 1573488016390734215675904000 := by
  rw [← show ((([(2, 3), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_1051, prime_quadB_1153, prime_quadB_940369, prime_quadB_6947861, prime_quadB_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446473 : Nat.totient 4729067536411289070045446473 = 4729067536411289070045446472 := by
  rw [← show ((([(4729067536411289070045446473, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_4729067536411289070045446473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446474 : Nat.totient 4729067536411289070045446474 = 2300627450146032520562649600 := by
  rw [← show ((([(2, 1), (37, 1), (63906318059612014460073601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_37, prime_quadB_63906318059612014460073601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446475 : Nat.totient 4729067536411289070045446475 = 2468876018011061253518131200 := by
  rw [← show ((([(3, 1), (5, 2), (97, 1), (109, 1), (571, 1), (41729, 1), (10653997, 1), (23492507, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_5, prime_quadB_97, prime_quadB_109, prime_quadB_571, prime_quadB_41729, prime_quadB_10653997, prime_quadB_23492507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446476 : Nat.totient 4729067536411289070045446476 = 2237238263396874131044008912 := by
  rw [← show ((([(2, 2), (19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_19, prime_quadB_787, prime_quadB_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446477 : Nat.totient 4729067536411289070045446477 = 3684987690710095379256192000 := by
  rw [← show ((([(7, 1), (11, 1), (61416461511834922987603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_7, prime_quadB_11, prime_quadB_61416461511834922987603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446478 : Nat.totient 4729067536411289070045446478 = 1455097703511165867706291200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (60629070979631911154428801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_3, prime_quadB_13, prime_quadB_60629070979631911154428801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446479 : Nat.totient 4729067536411289070045446479 = 4695238566185508250386746880 := by
  rw [← show ((([(157, 1), (2309, 1), (5519, 1), (5717, 1), (413450331680621, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_157, prime_quadB_2309, prime_quadB_5519, prime_quadB_5717, prime_quadB_413450331680621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446480 : Nat.totient 4729067536411289070045446480 = 1877819518107840331463297024 := by
  rw [← show ((([(2, 4), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_2, prime_quadB_5, prime_quadB_137, prime_quadB_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_quadB_4729067536411289070045446481 : Nat.totient 4729067536411289070045446481 = 3152627535595827192020653680 := by
  rw [← show ((([(3, 3), (37463, 1), (4675296946232667164981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729067536411289070045446481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_quadB_3, prime_quadB_37463, prime_quadB_4675296946232667164981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64QuadB : certifiedKill 1 4729067536411289070045446384 96 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_quadB_4729067536411289070045446385, phi_quadB_4729067536411289070045446386, phi_quadB_4729067536411289070045446387,
    phi_quadB_4729067536411289070045446388, phi_quadB_4729067536411289070045446389, phi_quadB_4729067536411289070045446390,
    phi_quadB_4729067536411289070045446391, phi_quadB_4729067536411289070045446392, phi_quadB_4729067536411289070045446393,
    phi_quadB_4729067536411289070045446394, phi_quadB_4729067536411289070045446395, phi_quadB_4729067536411289070045446396,
    phi_quadB_4729067536411289070045446397, phi_quadB_4729067536411289070045446398, phi_quadB_4729067536411289070045446399,
    phi_quadB_4729067536411289070045446400, phi_quadB_4729067536411289070045446401, phi_quadB_4729067536411289070045446402,
    phi_quadB_4729067536411289070045446403, phi_quadB_4729067536411289070045446404, phi_quadB_4729067536411289070045446405,
    phi_quadB_4729067536411289070045446406, phi_quadB_4729067536411289070045446407, phi_quadB_4729067536411289070045446408,
    phi_quadB_4729067536411289070045446409, phi_quadB_4729067536411289070045446410, phi_quadB_4729067536411289070045446411,
    phi_quadB_4729067536411289070045446412, phi_quadB_4729067536411289070045446413, phi_quadB_4729067536411289070045446414,
    phi_quadB_4729067536411289070045446415, phi_quadB_4729067536411289070045446416, phi_quadB_4729067536411289070045446417,
    phi_quadB_4729067536411289070045446418, phi_quadB_4729067536411289070045446419, phi_quadB_4729067536411289070045446420,
    phi_quadB_4729067536411289070045446421, phi_quadB_4729067536411289070045446422, phi_quadB_4729067536411289070045446423,
    phi_quadB_4729067536411289070045446424, phi_quadB_4729067536411289070045446425, phi_quadB_4729067536411289070045446426,
    phi_quadB_4729067536411289070045446427, phi_quadB_4729067536411289070045446428, phi_quadB_4729067536411289070045446429,
    phi_quadB_4729067536411289070045446430, phi_quadB_4729067536411289070045446431, phi_quadB_4729067536411289070045446432,
    phi_quadB_4729067536411289070045446433, phi_quadB_4729067536411289070045446434, phi_quadB_4729067536411289070045446435,
    phi_quadB_4729067536411289070045446436, phi_quadB_4729067536411289070045446437, phi_quadB_4729067536411289070045446438,
    phi_quadB_4729067536411289070045446439, phi_quadB_4729067536411289070045446440, phi_quadB_4729067536411289070045446441,
    phi_quadB_4729067536411289070045446442, phi_quadB_4729067536411289070045446443, phi_quadB_4729067536411289070045446444,
    phi_quadB_4729067536411289070045446445, phi_quadB_4729067536411289070045446446, phi_quadB_4729067536411289070045446447,
    phi_quadB_4729067536411289070045446448, phi_quadB_4729067536411289070045446449, phi_quadB_4729067536411289070045446450,
    phi_quadB_4729067536411289070045446451, phi_quadB_4729067536411289070045446452, phi_quadB_4729067536411289070045446453,
    phi_quadB_4729067536411289070045446454, phi_quadB_4729067536411289070045446455, phi_quadB_4729067536411289070045446456,
    phi_quadB_4729067536411289070045446457, phi_quadB_4729067536411289070045446458, phi_quadB_4729067536411289070045446459,
    phi_quadB_4729067536411289070045446460, phi_quadB_4729067536411289070045446461, phi_quadB_4729067536411289070045446462,
    phi_quadB_4729067536411289070045446463, phi_quadB_4729067536411289070045446464, phi_quadB_4729067536411289070045446465,
    phi_quadB_4729067536411289070045446466, phi_quadB_4729067536411289070045446467, phi_quadB_4729067536411289070045446468,
    phi_quadB_4729067536411289070045446469, phi_quadB_4729067536411289070045446470, phi_quadB_4729067536411289070045446471,
    phi_quadB_4729067536411289070045446472, phi_quadB_4729067536411289070045446473, phi_quadB_4729067536411289070045446474,
    phi_quadB_4729067536411289070045446475, phi_quadB_4729067536411289070045446476, phi_quadB_4729067536411289070045446477,
    phi_quadB_4729067536411289070045446478, phi_quadB_4729067536411289070045446479, phi_quadB_4729067536411289070045446480,
    phi_quadB_4729067536411289070045446481]

end TotientTailPeriodKiller
end Erdos249257
