import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open private
  prime_t64_2
  prime_t64_3
  prime_t64_5
  prime_t64_7
  prime_t64_11
  prime_t64_13
  prime_t64_17
  prime_t64_19
  prime_t64_23
  prime_t64_29
  prime_t64_31
  prime_t64_37
  prime_t64_41
  prime_t64_43
  prime_t64_47
  prime_t64_53
  prime_t64_59
  prime_t64_61
  prime_t64_67
  prime_t64_71
  prime_t64_73
  prime_t64_79
  prime_t64_83
  prime_t64_89
  prime_t64_97
  prime_t64_101
  prime_t64_103
  prime_t64_107
  prime_t64_109
  prime_t64_113
  prime_t64_137
  prime_t64_139
  prime_t64_149
  prime_t64_157
  prime_t64_163
  prime_t64_167
  prime_t64_179
  prime_t64_191
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_227
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_283
  prime_t64_307
  prime_t64_311
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_433
  prime_t64_439
  prime_t64_479
  prime_t64_499
  prime_t64_521
  prime_t64_563
  prime_t64_647
  prime_t64_683
  prime_t64_761
  prime_t64_883
  prime_t64_1483
  prime_t64_1579
  prime_t64_1619
  prime_t64_2027
  prime_t64_2281
  prime_t64_2377
  prime_t64_2417
  prime_t64_4327
  prime_t64_4787
  prime_t64_5009
  prime_t64_210193
  prime_t64_1214459
  prime_t64_2072201
  prime_t64_2567179
  from Erdos249257.DiagonalPincerCertificatesT64

private def thirtyTwoADFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyTwoADFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyTwoADFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyTwoADFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyTwoADFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyTwoADFastPow a n * thirtyTwoADFastPow a n * a
        else thirtyTwoADFastPow a n * thirtyTwoADFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyTwoAD_127 : Nat.Prime 127 := by norm_num

private theorem prime_thirtyTwoAD_131 : Nat.Prime 131 := by norm_num

private theorem prime_thirtyTwoAD_151 : Nat.Prime 151 := by norm_num

private theorem prime_thirtyTwoAD_181 : Nat.Prime 181 := by norm_num

private theorem prime_thirtyTwoAD_211 : Nat.Prime 211 := by norm_num

private theorem prime_thirtyTwoAD_241 : Nat.Prime 241 := by norm_num

private theorem prime_thirtyTwoAD_257 : Nat.Prime 257 := by norm_num

private theorem prime_thirtyTwoAD_271 : Nat.Prime 271 := by norm_num

private theorem prime_thirtyTwoAD_277 : Nat.Prime 277 := by norm_num

private theorem prime_thirtyTwoAD_293 : Nat.Prime 293 := by norm_num

private theorem prime_thirtyTwoAD_337 : Nat.Prime 337 := by norm_num

private theorem prime_thirtyTwoAD_347 : Nat.Prime 347 := by norm_num

private theorem prime_thirtyTwoAD_353 : Nat.Prime 353 := by norm_num

private theorem prime_thirtyTwoAD_367 : Nat.Prime 367 := by norm_num

private theorem prime_thirtyTwoAD_373 : Nat.Prime 373 := by norm_num

private theorem prime_thirtyTwoAD_379 : Nat.Prime 379 := by norm_num

private theorem prime_thirtyTwoAD_389 : Nat.Prime 389 := by norm_num

private theorem prime_thirtyTwoAD_397 : Nat.Prime 397 := by norm_num

private theorem prime_thirtyTwoAD_401 : Nat.Prime 401 := by norm_num

private theorem prime_thirtyTwoAD_419 : Nat.Prime 419 := by norm_num

private theorem prime_thirtyTwoAD_443 : Nat.Prime 443 := by norm_num

private theorem prime_thirtyTwoAD_449 : Nat.Prime 449 := by norm_num

private theorem prime_thirtyTwoAD_457 : Nat.Prime 457 := by norm_num

private theorem prime_thirtyTwoAD_503 : Nat.Prime 503 := by norm_num

private theorem prime_thirtyTwoAD_509 : Nat.Prime 509 := by norm_num

private theorem prime_thirtyTwoAD_547 : Nat.Prime 547 := by norm_num

private theorem prime_thirtyTwoAD_569 : Nat.Prime 569 := by norm_num

private theorem prime_thirtyTwoAD_571 : Nat.Prime 571 := by norm_num

private theorem prime_thirtyTwoAD_593 : Nat.Prime 593 := by norm_num

private theorem prime_thirtyTwoAD_619 : Nat.Prime 619 := by norm_num

private theorem prime_thirtyTwoAD_659 : Nat.Prime 659 := by norm_num

private theorem prime_thirtyTwoAD_677 : Nat.Prime 677 := by norm_num

private theorem prime_thirtyTwoAD_691 : Nat.Prime 691 := by norm_num

private theorem prime_thirtyTwoAD_701 : Nat.Prime 701 := by norm_num

private theorem prime_thirtyTwoAD_709 : Nat.Prime 709 := by norm_num

private theorem prime_thirtyTwoAD_739 : Nat.Prime 739 := by norm_num

private theorem prime_thirtyTwoAD_811 : Nat.Prime 811 := by norm_num

private theorem prime_thirtyTwoAD_821 : Nat.Prime 821 := by norm_num

private theorem prime_thirtyTwoAD_827 : Nat.Prime 827 := by norm_num

private theorem prime_thirtyTwoAD_839 : Nat.Prime 839 := by norm_num

private theorem prime_thirtyTwoAD_881 : Nat.Prime 881 := by norm_num

private theorem prime_thirtyTwoAD_907 : Nat.Prime 907 := by norm_num

private theorem prime_thirtyTwoAD_937 : Nat.Prime 937 := by norm_num

private theorem prime_thirtyTwoAD_967 : Nat.Prime 967 := by norm_num

private theorem prime_thirtyTwoAD_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_thirtyTwoAD_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_thirtyTwoAD_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_thirtyTwoAD_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_thirtyTwoAD_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_thirtyTwoAD_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_thirtyTwoAD_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_thirtyTwoAD_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_thirtyTwoAD_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_thirtyTwoAD_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_thirtyTwoAD_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_thirtyTwoAD_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_thirtyTwoAD_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_thirtyTwoAD_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_thirtyTwoAD_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_thirtyTwoAD_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_thirtyTwoAD_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_thirtyTwoAD_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_thirtyTwoAD_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_thirtyTwoAD_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_thirtyTwoAD_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_thirtyTwoAD_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_thirtyTwoAD_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_thirtyTwoAD_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_thirtyTwoAD_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_thirtyTwoAD_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_thirtyTwoAD_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_thirtyTwoAD_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_thirtyTwoAD_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_thirtyTwoAD_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_thirtyTwoAD_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_thirtyTwoAD_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_thirtyTwoAD_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_thirtyTwoAD_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_thirtyTwoAD_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_thirtyTwoAD_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_thirtyTwoAD_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_thirtyTwoAD_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_thirtyTwoAD_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_thirtyTwoAD_3061 : Nat.Prime 3061 := by norm_num

private theorem prime_thirtyTwoAD_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_thirtyTwoAD_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_thirtyTwoAD_3371 : Nat.Prime 3371 := by norm_num

private theorem prime_thirtyTwoAD_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_thirtyTwoAD_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_thirtyTwoAD_3533 : Nat.Prime 3533 := by norm_num

private theorem prime_thirtyTwoAD_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_thirtyTwoAD_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_thirtyTwoAD_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_thirtyTwoAD_4129 : Nat.Prime 4129 := by norm_num

private theorem prime_thirtyTwoAD_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_thirtyTwoAD_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_thirtyTwoAD_4483 : Nat.Prime 4483 := by norm_num

private theorem prime_thirtyTwoAD_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_thirtyTwoAD_4663 : Nat.Prime 4663 := by norm_num

private theorem prime_thirtyTwoAD_5147 : Nat.Prime 5147 := by norm_num

private theorem prime_thirtyTwoAD_5413 : Nat.Prime 5413 := by norm_num

private theorem prime_thirtyTwoAD_5479 : Nat.Prime 5479 := by norm_num

private theorem prime_thirtyTwoAD_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_thirtyTwoAD_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_thirtyTwoAD_6271 : Nat.Prime 6271 := by norm_num

private theorem prime_thirtyTwoAD_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_thirtyTwoAD_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_thirtyTwoAD_6421 : Nat.Prime 6421 := by norm_num

private theorem prime_thirtyTwoAD_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_thirtyTwoAD_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_thirtyTwoAD_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_thirtyTwoAD_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_thirtyTwoAD_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_thirtyTwoAD_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_thirtyTwoAD_7253 : Nat.Prime 7253 := by norm_num

private theorem prime_thirtyTwoAD_7349 : Nat.Prime 7349 := by norm_num

private theorem prime_thirtyTwoAD_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_thirtyTwoAD_7541 : Nat.Prime 7541 := by norm_num

private theorem prime_thirtyTwoAD_7549 : Nat.Prime 7549 := by norm_num

private theorem prime_thirtyTwoAD_7621 : Nat.Prime 7621 := by norm_num

private theorem prime_thirtyTwoAD_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_thirtyTwoAD_8699 : Nat.Prime 8699 := by norm_num

private theorem prime_thirtyTwoAD_8707 : Nat.Prime 8707 := by norm_num

private theorem prime_thirtyTwoAD_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_thirtyTwoAD_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_thirtyTwoAD_9011 : Nat.Prime 9011 := by norm_num

private theorem prime_thirtyTwoAD_9043 : Nat.Prime 9043 := by norm_num

private theorem prime_thirtyTwoAD_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_thirtyTwoAD_9283 : Nat.Prime 9283 := by norm_num

private theorem prime_thirtyTwoAD_9391 : Nat.Prime 9391 := by norm_num

private theorem prime_thirtyTwoAD_9739 : Nat.Prime 9739 := by norm_num

private theorem prime_thirtyTwoAD_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_thirtyTwoAD_10321 : Nat.Prime 10321 := by norm_num

private theorem prime_thirtyTwoAD_10333 : Nat.Prime 10333 := by norm_num

private theorem prime_thirtyTwoAD_10513 : Nat.Prime 10513 := by norm_num

private theorem prime_thirtyTwoAD_10909 : Nat.Prime 10909 := by norm_num

private theorem prime_thirtyTwoAD_11069 : Nat.Prime 11069 := by norm_num

private theorem prime_thirtyTwoAD_11393 : Nat.Prime 11393 := by norm_num

private theorem prime_thirtyTwoAD_11633 : Nat.Prime 11633 := by norm_num

private theorem prime_thirtyTwoAD_11839 : Nat.Prime 11839 := by norm_num

private theorem prime_thirtyTwoAD_11867 : Nat.Prime 11867 := by norm_num

private theorem prime_thirtyTwoAD_12097 : Nat.Prime 12097 := by norm_num

private theorem prime_thirtyTwoAD_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_thirtyTwoAD_12841 : Nat.Prime 12841 := by norm_num

private theorem prime_thirtyTwoAD_13309 : Nat.Prime 13309 := by norm_num

private theorem prime_thirtyTwoAD_13411 : Nat.Prime 13411 := by norm_num

private theorem prime_thirtyTwoAD_13693 : Nat.Prime 13693 := by norm_num

private theorem prime_thirtyTwoAD_13789 : Nat.Prime 13789 := by norm_num

private theorem prime_thirtyTwoAD_13967 : Nat.Prime 13967 := by norm_num

private theorem prime_thirtyTwoAD_14347 : Nat.Prime 14347 := by norm_num

private theorem prime_thirtyTwoAD_14741 : Nat.Prime 14741 := by norm_num

private theorem prime_thirtyTwoAD_15131 : Nat.Prime 15131 := by norm_num

private theorem prime_thirtyTwoAD_15287 : Nat.Prime 15287 := by norm_num

private theorem prime_thirtyTwoAD_15797 : Nat.Prime 15797 := by norm_num

private theorem prime_thirtyTwoAD_15803 : Nat.Prime 15803 := by norm_num

private theorem prime_thirtyTwoAD_15889 : Nat.Prime 15889 := by norm_num

private theorem prime_thirtyTwoAD_16301 : Nat.Prime 16301 := by norm_num

private theorem prime_thirtyTwoAD_17417 : Nat.Prime 17417 := by norm_num

private theorem prime_thirtyTwoAD_17491 : Nat.Prime 17491 := by norm_num

private theorem prime_thirtyTwoAD_17573 : Nat.Prime 17573 := by norm_num

private theorem prime_thirtyTwoAD_17669 : Nat.Prime 17669 := by norm_num

private theorem prime_thirtyTwoAD_17737 : Nat.Prime 17737 := by norm_num

private theorem prime_thirtyTwoAD_18089 : Nat.Prime 18089 := by norm_num

private theorem prime_thirtyTwoAD_18899 : Nat.Prime 18899 := by norm_num

private theorem prime_thirtyTwoAD_18919 : Nat.Prime 18919 := by norm_num

private theorem prime_thirtyTwoAD_18979 : Nat.Prime 18979 := by norm_num

private theorem prime_thirtyTwoAD_20183 : Nat.Prime 20183 := by norm_num

private theorem prime_thirtyTwoAD_20641 : Nat.Prime 20641 := by norm_num

private theorem prime_thirtyTwoAD_22973 : Nat.Prime 22973 := by norm_num

private theorem prime_thirtyTwoAD_23417 : Nat.Prime 23417 := by norm_num

private theorem prime_thirtyTwoAD_23761 : Nat.Prime 23761 := by norm_num

private theorem prime_thirtyTwoAD_24103 : Nat.Prime 24103 := by norm_num

private theorem prime_thirtyTwoAD_24971 : Nat.Prime 24971 := by norm_num

private theorem prime_thirtyTwoAD_26261 : Nat.Prime 26261 := by norm_num

private theorem prime_thirtyTwoAD_26863 : Nat.Prime 26863 := by norm_num

private theorem prime_thirtyTwoAD_27143 : Nat.Prime 27143 := by norm_num

private theorem prime_thirtyTwoAD_27733 : Nat.Prime 27733 := by norm_num

private theorem prime_thirtyTwoAD_28183 : Nat.Prime 28183 := by norm_num

private theorem prime_thirtyTwoAD_28439 : Nat.Prime 28439 := by norm_num

private theorem prime_thirtyTwoAD_29363 : Nat.Prime 29363 := by norm_num

private theorem prime_thirtyTwoAD_30557 : Nat.Prime 30557 := by norm_num

private theorem prime_thirtyTwoAD_31183 : Nat.Prime 31183 := by norm_num

private theorem prime_thirtyTwoAD_32321 : Nat.Prime 32321 := by norm_num

private theorem prime_thirtyTwoAD_34301 : Nat.Prime 34301 := by norm_num

private theorem prime_thirtyTwoAD_34739 : Nat.Prime 34739 := by norm_num

private theorem prime_thirtyTwoAD_35753 : Nat.Prime 35753 := by norm_num

private theorem prime_thirtyTwoAD_36341 : Nat.Prime 36341 := by norm_num

private theorem prime_thirtyTwoAD_36457 : Nat.Prime 36457 := by norm_num

private theorem prime_thirtyTwoAD_37573 : Nat.Prime 37573 := by norm_num

private theorem prime_thirtyTwoAD_39343 : Nat.Prime 39343 := by norm_num

private theorem prime_thirtyTwoAD_43867 : Nat.Prime 43867 := by norm_num

private theorem prime_thirtyTwoAD_46271 : Nat.Prime 46271 := by norm_num

private theorem prime_thirtyTwoAD_46523 : Nat.Prime 46523 := by norm_num

private theorem prime_thirtyTwoAD_46679 : Nat.Prime 46679 := by norm_num

private theorem prime_thirtyTwoAD_50227 : Nat.Prime 50227 := by norm_num

private theorem prime_thirtyTwoAD_50821 : Nat.Prime 50821 := by norm_num

private theorem prime_thirtyTwoAD_53269 : Nat.Prime 53269 := by norm_num

private theorem prime_thirtyTwoAD_55313 : Nat.Prime 55313 := by norm_num

private theorem prime_thirtyTwoAD_55603 : Nat.Prime 55603 := by norm_num

private theorem prime_thirtyTwoAD_55897 : Nat.Prime 55897 := by norm_num

private theorem prime_thirtyTwoAD_58337 : Nat.Prime 58337 := by norm_num

private theorem prime_thirtyTwoAD_59333 : Nat.Prime 59333 := by norm_num

private theorem prime_thirtyTwoAD_59513 : Nat.Prime 59513 := by norm_num

private theorem prime_thirtyTwoAD_60427 : Nat.Prime 60427 := by norm_num

private theorem prime_thirtyTwoAD_61379 : Nat.Prime 61379 := by norm_num

private theorem prime_thirtyTwoAD_61667 : Nat.Prime 61667 := by norm_num

private theorem prime_thirtyTwoAD_63353 : Nat.Prime 63353 := by norm_num

private theorem prime_thirtyTwoAD_64091 : Nat.Prime 64091 := by norm_num

private theorem prime_thirtyTwoAD_66553 : Nat.Prime 66553 := by norm_num

private theorem prime_thirtyTwoAD_66569 : Nat.Prime 66569 := by norm_num

private theorem prime_thirtyTwoAD_68891 : Nat.Prime 68891 := by norm_num

private theorem prime_thirtyTwoAD_71171 : Nat.Prime 71171 := by norm_num

private theorem prime_thirtyTwoAD_73141 : Nat.Prime 73141 := by norm_num

private theorem prime_thirtyTwoAD_78539 : Nat.Prime 78539 := by norm_num

private theorem prime_thirtyTwoAD_80191 : Nat.Prime 80191 := by norm_num

private theorem prime_thirtyTwoAD_81769 : Nat.Prime 81769 := by norm_num

private theorem prime_thirtyTwoAD_82301 : Nat.Prime 82301 := by norm_num

private theorem prime_thirtyTwoAD_82889 : Nat.Prime 82889 := by norm_num

private theorem prime_thirtyTwoAD_85243 : Nat.Prime 85243 := by norm_num

private theorem prime_thirtyTwoAD_85313 : Nat.Prime 85313 := by norm_num

private theorem prime_thirtyTwoAD_85991 : Nat.Prime 85991 := by norm_num

private theorem prime_thirtyTwoAD_86201 : Nat.Prime 86201 := by norm_num

private theorem prime_thirtyTwoAD_87337 : Nat.Prime 87337 := by norm_num

private theorem prime_thirtyTwoAD_89269 : Nat.Prime 89269 := by norm_num

private theorem prime_thirtyTwoAD_90031 : Nat.Prime 90031 := by norm_num

private theorem prime_thirtyTwoAD_94321 : Nat.Prime 94321 := by norm_num

private theorem prime_thirtyTwoAD_97373 : Nat.Prime 97373 := by norm_num

private theorem prime_thirtyTwoAD_100193 : Nat.Prime 100193 := by norm_num

private theorem prime_thirtyTwoAD_102593 : Nat.Prime 102593 := by norm_num

private theorem prime_thirtyTwoAD_103393 : Nat.Prime 103393 := by norm_num

private theorem prime_thirtyTwoAD_106363 : Nat.Prime 106363 := by norm_num

private theorem prime_thirtyTwoAD_112571 : Nat.Prime 112571 := by norm_num

private theorem prime_thirtyTwoAD_114067 : Nat.Prime 114067 := by norm_num

private theorem prime_thirtyTwoAD_122957 : Nat.Prime 122957 := by norm_num

private theorem prime_thirtyTwoAD_123701 : Nat.Prime 123701 := by norm_num

private theorem prime_thirtyTwoAD_130513 : Nat.Prime 130513 := by norm_num

private theorem prime_thirtyTwoAD_144577 : Nat.Prime 144577 := by norm_num

private theorem prime_thirtyTwoAD_148721 : Nat.Prime 148721 := by norm_num

private theorem prime_thirtyTwoAD_163987 : Nat.Prime 163987 := by norm_num

private theorem prime_thirtyTwoAD_180497 : Nat.Prime 180497 := by norm_num

private theorem prime_thirtyTwoAD_185177 : Nat.Prime 185177 := by norm_num

private theorem prime_thirtyTwoAD_201589 : Nat.Prime 201589 := by norm_num

private theorem prime_thirtyTwoAD_206813 : Nat.Prime 206813 := by norm_num

private theorem prime_thirtyTwoAD_229519 : Nat.Prime 229519 := by norm_num

private theorem prime_thirtyTwoAD_239963 : Nat.Prime 239963 := by norm_num

private theorem prime_thirtyTwoAD_278029 : Nat.Prime 278029 := by norm_num

private theorem prime_thirtyTwoAD_293081 : Nat.Prime 293081 := by norm_num

private theorem prime_thirtyTwoAD_299287 : Nat.Prime 299287 := by norm_num

private theorem prime_thirtyTwoAD_301993 : Nat.Prime 301993 := by norm_num

private theorem prime_thirtyTwoAD_316583 : Nat.Prime 316583 := by norm_num

private theorem prime_thirtyTwoAD_327619 : Nat.Prime 327619 := by norm_num

private theorem prime_thirtyTwoAD_327797 : Nat.Prime 327797 := by norm_num

private theorem prime_thirtyTwoAD_349667 : Nat.Prime 349667 := by norm_num

private theorem prime_thirtyTwoAD_357559 : Nat.Prime 357559 := by norm_num

private theorem prime_thirtyTwoAD_381761 : Nat.Prime 381761 := by norm_num

private theorem prime_thirtyTwoAD_382709 : Nat.Prime 382709 := by norm_num

private theorem prime_thirtyTwoAD_382747 : Nat.Prime 382747 := by norm_num

private theorem prime_thirtyTwoAD_384973 : Nat.Prime 384973 := by norm_num

private theorem prime_thirtyTwoAD_396479 : Nat.Prime 396479 := by norm_num

private theorem prime_thirtyTwoAD_402137 : Nat.Prime 402137 := by norm_num

private theorem prime_thirtyTwoAD_455899 : Nat.Prime 455899 := by norm_num

private theorem prime_thirtyTwoAD_474629 : Nat.Prime 474629 := by norm_num

private theorem prime_thirtyTwoAD_497291 : Nat.Prime 497291 := by norm_num

private theorem prime_thirtyTwoAD_573143 : Nat.Prime 573143 := by norm_num

private theorem prime_thirtyTwoAD_576617 : Nat.Prime 576617 := by norm_num

private theorem prime_thirtyTwoAD_586471 : Nat.Prime 586471 := by norm_num

private theorem prime_thirtyTwoAD_595201 : Nat.Prime 595201 := by norm_num

private theorem prime_thirtyTwoAD_611887 : Nat.Prime 611887 := by norm_num

private theorem prime_thirtyTwoAD_622967 : Nat.Prime 622967 := by norm_num

private theorem prime_thirtyTwoAD_644549 : Nat.Prime 644549 := by norm_num

private theorem prime_thirtyTwoAD_656023 : Nat.Prime 656023 := by norm_num

private theorem prime_thirtyTwoAD_665053 : Nat.Prime 665053 := by norm_num

private theorem prime_thirtyTwoAD_674701 : Nat.Prime 674701 := by norm_num

private theorem prime_thirtyTwoAD_761203 : Nat.Prime 761203 := by norm_num

private theorem prime_thirtyTwoAD_775189 : Nat.Prime 775189 := by norm_num

private theorem prime_thirtyTwoAD_776987 : Nat.Prime 776987 := by norm_num

private theorem prime_thirtyTwoAD_790567 : Nat.Prime 790567 := by norm_num

private theorem prime_thirtyTwoAD_813613 : Nat.Prime 813613 := by norm_num

private theorem prime_thirtyTwoAD_854771 : Nat.Prime 854771 := by norm_num

private theorem prime_thirtyTwoAD_931883 : Nat.Prime 931883 := by norm_num

private theorem prime_thirtyTwoAD_1036459 : Nat.Prime 1036459 := by norm_num

private theorem prime_thirtyTwoAD_1257209 : Nat.Prime 1257209 := by norm_num

private theorem prime_thirtyTwoAD_1265779 : Nat.Prime 1265779 := by norm_num

private theorem prime_thirtyTwoAD_1342139 : Nat.Prime 1342139 := by norm_num

private theorem prime_thirtyTwoAD_1395137 : Nat.Prime 1395137 := by norm_num

private theorem prime_thirtyTwoAD_1427389 : Nat.Prime 1427389 := by norm_num

private theorem prime_thirtyTwoAD_1459457 : Nat.Prime 1459457 := by norm_num

private theorem prime_thirtyTwoAD_1640147 : Nat.Prime 1640147 := by norm_num

private theorem prime_thirtyTwoAD_1694851 : Nat.Prime 1694851 := by norm_num

private theorem prime_thirtyTwoAD_1740097 : Nat.Prime 1740097 := by norm_num

private theorem prime_thirtyTwoAD_1936747 : Nat.Prime 1936747 := by norm_num

private theorem prime_thirtyTwoAD_1958569 : Nat.Prime 1958569 := by norm_num

private theorem prime_thirtyTwoAD_2015141 : Nat.Prime 2015141 := by norm_num

private theorem prime_thirtyTwoAD_2095193 : Nat.Prime 2095193 := by norm_num

private theorem prime_thirtyTwoAD_2126213 : Nat.Prime 2126213 := by norm_num

private theorem prime_thirtyTwoAD_2320481 : Nat.Prime 2320481 := by norm_num

private theorem prime_thirtyTwoAD_2339107 : Nat.Prime 2339107 := by norm_num

private theorem prime_thirtyTwoAD_2379253 : Nat.Prime 2379253 := by norm_num

private theorem prime_thirtyTwoAD_2504251 : Nat.Prime 2504251 := by norm_num

private theorem prime_thirtyTwoAD_2609311 : Nat.Prime 2609311 := by norm_num

private theorem prime_thirtyTwoAD_2751247 : Nat.Prime 2751247 := by norm_num

private theorem prime_thirtyTwoAD_2813227 : Nat.Prime 2813227 := by norm_num

private theorem prime_thirtyTwoAD_2818667 : Nat.Prime 2818667 := by norm_num

private theorem prime_thirtyTwoAD_3972037 : Nat.Prime 3972037 := by norm_num

private theorem prime_thirtyTwoAD_4187801 : Nat.Prime 4187801 := by norm_num

private theorem prime_thirtyTwoAD_4203707 : Nat.Prime 4203707 := by norm_num

private theorem prime_thirtyTwoAD_4315799 : Nat.Prime 4315799 := by norm_num

private theorem prime_thirtyTwoAD_4924417 : Nat.Prime 4924417 := by norm_num

private theorem prime_thirtyTwoAD_5266519 : Nat.Prime 5266519 := by norm_num

private theorem prime_thirtyTwoAD_5276861 : Nat.Prime 5276861 := by norm_num

private theorem prime_thirtyTwoAD_5314121 : Nat.Prime 5314121 := by norm_num

private theorem prime_thirtyTwoAD_6126727 : Nat.Prime 6126727 := by norm_num

private theorem prime_thirtyTwoAD_6180901 : Nat.Prime 6180901 := by norm_num

private theorem prime_thirtyTwoAD_6213533 : Nat.Prime 6213533 := by norm_num

private theorem prime_thirtyTwoAD_6585251 : Nat.Prime 6585251 := by norm_num

private theorem prime_thirtyTwoAD_6850243 : Nat.Prime 6850243 := by norm_num

private theorem prime_thirtyTwoAD_7041049 : Nat.Prime 7041049 := by norm_num

private theorem prime_thirtyTwoAD_7220867 : Nat.Prime 7220867 := by norm_num

private theorem prime_thirtyTwoAD_7281277 : Nat.Prime 7281277 := by norm_num

private theorem prime_thirtyTwoAD_7690391 : Nat.Prime 7690391 := by norm_num

private theorem prime_thirtyTwoAD_8265919 : Nat.Prime 8265919 := by norm_num

private theorem prime_thirtyTwoAD_8651953 : Nat.Prime 8651953 := by norm_num

private theorem prime_thirtyTwoAD_8717677 : Nat.Prime 8717677 := by norm_num

private theorem prime_thirtyTwoAD_9042907 : Nat.Prime 9042907 := by norm_num

private theorem prime_thirtyTwoAD_9124861 : Nat.Prime 9124861 := by norm_num

private theorem prime_thirtyTwoAD_9339191 : Nat.Prime 9339191 := by norm_num

private theorem prime_thirtyTwoAD_9420721 : Nat.Prime 9420721 := by norm_num

private theorem prime_thirtyTwoAD_11366041 : Nat.Prime 11366041 := by
  apply lucas_primality 11366041 (17 : ZMod 11366041)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) = 11366041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_1933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11366041) ^ 5683020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 11366041) ^ 3788680 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 11366041) ^ 2273208 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 11366041) ^ 1623720 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 11366041) ^ 5880 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_11566843 : Nat.Prime 11566843 := by
  apply lucas_primality 11566843 (5 : ZMod 11566843)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (39343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (39343, 1)] : List FactorBlock).map factorBlockValue).prod) = 11566843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_39343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11566843) ^ 5783421 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11566843) ^ 3855614 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11566843) ^ 1652406 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11566843) ^ 294 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_12513617 : Nat.Prime 12513617 := by
  apply lucas_primality 12513617 (3 : ZMod 12513617)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (149, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (149, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 12513617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_149
      · exact prime_thirtyTwoAD_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12513617) ^ 6256808 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 12513617) ^ 431504 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 12513617) ^ 83984 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 12513617) ^ 69136 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_13969493 : Nat.Prime 13969493 := by
  apply lucas_primality 13969493 (2 : ZMod 13969493)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 13969493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_107
      · exact prime_thirtyTwoAD_127
      · exact prime_thirtyTwoAD_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13969493) ^ 6984746 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969493) ^ 130556 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969493) ^ 109996 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969493) ^ 54356 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_14218879 : Nat.Prime 14218879 := by
  apply lucas_primality 14218879 (3 : ZMod 14218879)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (37, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (37, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 14218879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14218879) ^ 7109439 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 14218879) ^ 4739626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 14218879) ^ 748362 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 14218879) ^ 384294 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 14218879) ^ 4218 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_15857351 : Nat.Prime 15857351 := by
  apply lucas_primality 15857351 (17 : ZMod 15857351)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 15857351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 15857351) ^ 7928675 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 15857351) ^ 3171470 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 15857351) ^ 689450 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 15857351) ^ 1150 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_16205789 : Nat.Prime 16205789 := by
  apply lucas_primality 16205789 (2 : ZMod 16205789)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (86201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (86201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16205789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_thirtyTwoAD_86201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16205789) ^ 8102894 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 16205789) ^ 344804 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 16205789) ^ 188 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_17478479 : Nat.Prime 17478479 := by
  apply lucas_primality 17478479 (7 : ZMod 17478479)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (433, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (433, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) = 17478479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_433
      · exact prime_thirtyTwoAD_20183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 17478479) ^ 8739239 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 17478479) ^ 40366 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 17478479) ^ 866 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_18480383 : Nat.Prime 18480383 := by
  apply lucas_primality 18480383 (5 : ZMod 18480383)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2417, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2417, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) = 18480383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_2417
      · exact prime_thirtyTwoAD_3823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18480383) ^ 9240191 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18480383) ^ 7646 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18480383) ^ 4834 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_23255671 : Nat.Prime 23255671 := by
  apply lucas_primality 23255671 (6 : ZMod 23255671)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod) = 23255671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_775189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 23255671) ^ 11627835 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 7751890 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 4651134 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 30 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_24581699 : Nat.Prime 24581699 := by
  apply lucas_primality 24581699 (2 : ZMod 24581699)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (396479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (396479, 1)] : List FactorBlock).map factorBlockValue).prod) = 24581699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_thirtyTwoAD_396479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24581699) ^ 12290849 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581699) ^ 792958 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 24581699) ^ 62 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_25331881 : Nat.Prime 25331881 := by
  apply lucas_primality 25331881 (17 : ZMod 25331881)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 25331881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_thirtyTwoAD_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 25331881) ^ 12665940 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 8443960 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 5066376 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 3618840 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 477960 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 44520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_25817069 : Nat.Prime 25817069 := by
  apply lucas_primality 25817069 (2 : ZMod 25817069)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod) = 25817069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_127
      · exact prime_thirtyTwoAD_50821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25817069) ^ 12908534 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 25817069) ^ 203284 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 25817069) ^ 508 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_26841377 : Nat.Prime 26841377 := by
  apply lucas_primality 26841377 (3 : ZMod 26841377)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (131, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (131, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 26841377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_131
      · exact prime_thirtyTwoAD_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26841377) ^ 13420688 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 26841377) ^ 1412704 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 26841377) ^ 204896 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 26841377) ^ 79648 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_26977667 : Nat.Prime 26977667 := by
  apply lucas_primality 26977667 (2 : ZMod 26977667)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (586471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (586471, 1)] : List FactorBlock).map factorBlockValue).prod) = 26977667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_586471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26977667) ^ 13488833 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 26977667) ^ 1172942 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 26977667) ^ 46 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_27902741 : Nat.Prime 27902741 := by
  apply lucas_primality 27902741 (2 : ZMod 27902741)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1395137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1395137, 1)] : List FactorBlock).map factorBlockValue).prod) = 27902741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_1395137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27902741) ^ 13951370 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 27902741) ^ 5580548 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 27902741) ^ 20 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_30987953 : Nat.Prime 30987953 := by
  apply lucas_primality 30987953 (3 : ZMod 30987953)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1936747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1936747, 1)] : List FactorBlock).map factorBlockValue).prod) = 30987953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_1936747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 30987953) ^ 15493976 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 30987953) ^ 16 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_32731453 : Nat.Prime 32731453 := by
  apply lucas_primality 32731453 (2 : ZMod 32731453)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (19, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (19, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 32731453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32731453) ^ 16365726 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 32731453) ^ 10910484 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 32731453) ^ 2517804 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 32731453) ^ 1722708 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 32731453) ^ 80028 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_39926713 : Nat.Prime 39926713 := by
  apply lucas_primality 39926713 (11 : ZMod 39926713)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 39926713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39926713) ^ 19963356 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 13308904 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 5703816 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 1735944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 39926713) ^ 3864 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_41136839 : Nat.Prime 41136839 := by
  apply lucas_primality 41136839 (7 : ZMod 41136839)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) = 41136839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_71171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 41136839) ^ 20568419 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 2419814 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 41136839) ^ 578 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_42001217 : Nat.Prime 42001217 := by
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42001217) ^ 21000608 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 1135168 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 2368 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_42312103 : Nat.Prime 42312103 := by
  apply lucas_primality 42312103 (5 : ZMod 42312103)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (34739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (34739, 1)] : List FactorBlock).map factorBlockValue).prod) = 42312103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_thirtyTwoAD_34739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42312103) ^ 21156051 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 42312103) ^ 14104034 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 42312103) ^ 6044586 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 42312103) ^ 1459038 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 42312103) ^ 1218 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_43687663 : Nat.Prime 43687663 := by
  apply lucas_primality 43687663 (3 : ZMod 43687663)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7281277, 1)] : List FactorBlock).map factorBlockValue).prod) = 43687663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_7281277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43687663) ^ 21843831 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 14562554 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687663) ^ 6 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_44317043 : Nat.Prime 44317043 := by
  apply lucas_primality 44317043 (2 : ZMod 44317043)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (31, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (31, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) = 44317043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_31
      · exact prime_thirtyTwoAD_9283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44317043) ^ 22158521 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 44317043) ^ 6331006 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 44317043) ^ 4028822 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 44317043) ^ 1429582 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 44317043) ^ 4774 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_51634139 : Nat.Prime 51634139 := by
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod) = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51634139) ^ 25817069 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 51634139) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_52177423 : Nat.Prime 52177423 := by
  apply lucas_primality 52177423 (6 : ZMod 52177423)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (790567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (790567, 1)] : List FactorBlock).map factorBlockValue).prod) = 52177423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_790567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 52177423) ^ 26088711 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 52177423) ^ 17392474 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 52177423) ^ 4743402 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 52177423) ^ 66 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_52837133 : Nat.Prime 52837133 := by
  apply lucas_primality 52837133 (2 : ZMod 52837133)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (503, 1), (26261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (503, 1), (26261, 1)] : List FactorBlock).map factorBlockValue).prod) = 52837133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_503
      · exact prime_thirtyTwoAD_26261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52837133) ^ 26418566 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 52837133) ^ 105044 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 52837133) ^ 2012 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_56016929 : Nat.Prime 56016929 := by
  apply lucas_primality 56016929 (3 : ZMod 56016929)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (233, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (233, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) = 56016929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_233
      · exact prime_t64_683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56016929) ^ 28008464 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 56016929) ^ 5092448 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 56016929) ^ 240416 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 56016929) ^ 82016 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_60672923 : Nat.Prime 60672923 := by
  apply lucas_primality 60672923 (2 : ZMod 60672923)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (101, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (101, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) = 60672923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_4483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60672923) ^ 30336461 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 905566 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 600722 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60672923) ^ 13534 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_62596619 : Nat.Prime 62596619 := by
  apply lucas_primality 62596619 (2 : ZMod 62596619)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (37573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (37573, 1)] : List FactorBlock).map factorBlockValue).prod) = 62596619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_37573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62596619) ^ 31298309 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 62596619) ^ 8942374 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 62596619) ^ 3682154 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 62596619) ^ 1666 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_63198229 : Nat.Prime 63198229 := by
  apply lucas_primality 63198229 (2 : ZMod 63198229)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5266519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5266519, 1)] : List FactorBlock).map factorBlockValue).prod) = 63198229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_5266519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63198229) ^ 31599114 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 63198229) ^ 21066076 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 63198229) ^ 12 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_65642413 : Nat.Prime 65642413 := by
  apply lucas_primality 65642413 (2 : ZMod 65642413)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (497291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (497291, 1)] : List FactorBlock).map factorBlockValue).prod) = 65642413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_497291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65642413) ^ 32821206 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 65642413) ^ 21880804 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 65642413) ^ 5967492 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 65642413) ^ 132 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_67074817 : Nat.Prime 67074817 := by
  apply lucas_primality 67074817 (15 : ZMod 67074817)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (87337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (87337, 1)] : List FactorBlock).map factorBlockValue).prod) = 67074817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_87337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 67074817) ^ 33537408 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (15 : ZMod 67074817) ^ 22358272 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (15 : ZMod 67074817) ^ 768 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_70150373 : Nat.Prime 70150373 := by
  apply lucas_primality 70150373 (2 : ZMod 70150373)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (43, 1), (73, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 70150373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_43
      · exact prime_t64_73
      · exact prime_thirtyTwoAD_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70150373) ^ 35075186 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1895956 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 1631404 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 960964 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 70150373) ^ 464572 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_1901
      · exact prime_thirtyTwoAD_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_75581171 : Nat.Prime 75581171 := by
  apply lucas_primality 75581171 (2 : ZMod 75581171)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) = 75581171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_thirtyTwoAD_22973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75581171) ^ 37790585 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 15116234 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 10797310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 1608110 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 75581171) ^ 3290 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_87023341 : Nat.Prime 87023341 := by
  apply lucas_primality 87023341 (2 : ZMod 87023341)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (28439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (28439, 1)] : List FactorBlock).map factorBlockValue).prod) = 87023341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_28439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87023341) ^ 43511670 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87023341) ^ 29007780 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87023341) ^ 17404668 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87023341) ^ 5119020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87023341) ^ 3060 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_87998107 : Nat.Prime 87998107 := by
  apply lucas_primality 87998107 (2 : ZMod 87998107)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2095193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2095193, 1)] : List FactorBlock).map factorBlockValue).prod) = 87998107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_2095193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87998107) ^ 43999053 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87998107) ^ 29332702 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87998107) ^ 12571158 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 87998107) ^ 42 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_100888969 : Nat.Prime 100888969 := by
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod) = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100888969) ^ 50444484 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 33629656 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 24 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_110748857 : Nat.Prime 110748857 := by
  apply lucas_primality 110748857 (3 : ZMod 110748857)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (367, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (367, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) = 110748857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_367
      · exact prime_t64_563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110748857) ^ 55374428 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 110748857) ^ 1652968 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 110748857) ^ 301768 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 110748857) ^ 196712 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_115555873 : Nat.Prime 115555873 := by
  apply lucas_primality 115555873 (14 : ZMod 115555873)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) = 115555873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_63353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 115555873) ^ 57777936 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 115555873) ^ 38518624 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 115555873) ^ 6081888 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 115555873) ^ 1824 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_122761591 : Nat.Prime 122761591 := by
  apply lucas_primality 122761591 (14 : ZMod 122761591)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (137, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (137, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 122761591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_137
      · exact prime_t64_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 122761591) ^ 61380795 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 40920530 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 24552318 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 17537370 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 7221270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 896070 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 122761591) ^ 489090 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_135660131 : Nat.Prime 135660131 := by
  apply lucas_primality 135660131 (2 : ZMod 135660131)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (127, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (127, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) = 135660131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_127
      · exact prime_thirtyTwoAD_2887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135660131) ^ 67830065 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 135660131) ^ 27132026 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 135660131) ^ 3666490 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 135660131) ^ 1068190 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 135660131) ^ 46990 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_144038591 : Nat.Prime 144038591 := by
  apply lucas_primality 144038591 (7 : ZMod 144038591)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 144038591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_827
      · exact prime_thirtyTwoAD_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144038591) ^ 72019295 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 28807718 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 174170 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 8270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_147688193 : Nat.Prime 147688193 := by
  apply lucas_primality 147688193 (3 : ZMod 147688193)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (137, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (137, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 147688193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_137
      · exact prime_thirtyTwoAD_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 147688193) ^ 73844096 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 147688193) ^ 1078016 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 147688193) ^ 35072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_179646739 : Nat.Prime 179646739 := by
  apply lucas_primality 179646739 (10 : ZMod 179646739)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4663, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4663, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) = 179646739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_4663
      · exact prime_thirtyTwoAD_6421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 179646739) ^ 89823369 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 179646739) ^ 59882246 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 179646739) ^ 38526 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 179646739) ^ 27978 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_194261939 : Nat.Prime 194261939 := by
  apply lucas_primality 194261939 (2 : ZMod 194261939)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1117, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1117, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) = 194261939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_1117
      · exact prime_thirtyTwoAD_6689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 194261939) ^ 97130969 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 194261939) ^ 14943226 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 194261939) ^ 173914 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 194261939) ^ 29042 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_200734711 : Nat.Prime 200734711 := by
  apply lucas_primality 200734711 (3 : ZMod 200734711)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (97, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (97, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) = 200734711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_97
      · exact prime_thirtyTwoAD_6271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 200734711) ^ 100367355 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 200734711) ^ 66911570 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 200734711) ^ 40146942 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 200734711) ^ 18248610 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 200734711) ^ 2069430 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 200734711) ^ 32010 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_219959393 : Nat.Prime 219959393 := by
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod) = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219959393) ^ 109979696 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 3282976 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 2144 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_224359867 : Nat.Prime 224359867 := by
  apply lucas_primality 224359867 (2 : ZMod 224359867)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod) = 224359867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_656023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224359867) ^ 112179933 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 74786622 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 11808414 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 342 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_232001521 : Nat.Prime 232001521 := by
  apply lucas_primality 232001521 (7 : ZMod 232001521)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (31, 1), (31183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (31, 1), (31183, 1)] : List FactorBlock).map factorBlockValue).prod) = 232001521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_thirtyTwoAD_31183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 232001521) ^ 116000760 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 77333840 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 46400304 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 7483920 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 232001521) ^ 7440 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_240408097 : Nat.Prime 240408097 := by
  apply lucas_primality 240408097 (5 : ZMod 240408097)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2504251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2504251, 1)] : List FactorBlock).map factorBlockValue).prod) = 240408097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_2504251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 240408097) ^ 120204048 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 240408097) ^ 80136032 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 240408097) ^ 96 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_266476337 : Nat.Prime 266476337 := by
  apply lucas_primality 266476337 (3 : ZMod 266476337)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2379253, 1)] : List FactorBlock).map factorBlockValue).prod) = 266476337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_2379253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266476337) ^ 133238168 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 38068048 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 266476337) ^ 112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_289267687 : Nat.Prime 289267687 := by
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod) = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 289267687) ^ 144633843 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 96422562 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 486 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_308134529 : Nat.Prime 308134529 := by
  apply lucas_primality 308134529 (3 : ZMod 308134529)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (185177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (185177, 1)] : List FactorBlock).map factorBlockValue).prod) = 308134529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_185177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 308134529) ^ 154067264 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 308134529) ^ 23702656 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 308134529) ^ 1664 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_329747923 : Nat.Prime 329747923 := by
  apply lucas_primality 329747923 (2 : ZMod 329747923)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (29, 1), (37, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (29, 1), (37, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 329747923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 329747923) ^ 164873961 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 329747923) ^ 109915974 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 329747923) ^ 47106846 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 329747923) ^ 11370618 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 329747923) ^ 8912106 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 329747923) ^ 1216782 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_362808133 : Nat.Prime 362808133 := by
  apply lucas_primality 362808133 (5 : ZMod 362808133)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (382709, 1)] : List FactorBlock).map factorBlockValue).prod) = 362808133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_79
      · exact prime_thirtyTwoAD_382709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 362808133) ^ 181404066 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 120936044 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 4592508 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 362808133) ^ 948 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_364037539 : Nat.Prime 364037539 := by
  apply lucas_primality 364037539 (2 : ZMod 364037539)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (60672923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (60672923, 1)] : List FactorBlock).map factorBlockValue).prod) = 364037539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_60672923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 364037539) ^ 182018769 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 364037539) ^ 121345846 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 364037539) ^ 6 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_388523879 : Nat.Prime 388523879 := by
  apply lucas_primality 388523879 (7 : ZMod 388523879)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (194261939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (194261939, 1)] : List FactorBlock).map factorBlockValue).prod) = 388523879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_194261939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 388523879) ^ 194261939 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 388523879) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_415741019 : Nat.Prime 415741019 := by
  apply lucas_primality 415741019 (2 : ZMod 415741019)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (379, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (379, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 415741019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_379
      · exact prime_thirtyTwoAD_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 415741019) ^ 207870509 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 59391574 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 37794638 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 24455354 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 1096942 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 415741019) ^ 992222 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_419084791 : Nat.Prime 419084791 := by
  apply lucas_primality 419084791 (3 : ZMod 419084791)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13969493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13969493, 1)] : List FactorBlock).map factorBlockValue).prod) = 419084791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_13969493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 419084791) ^ 209542395 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 419084791) ^ 139694930 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 419084791) ^ 83816958 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 419084791) ^ 30 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_439297513 : Nat.Prime 439297513 := by
  apply lucas_primality 439297513 (5 : ZMod 439297513)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (223, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (223, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 439297513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_79
      · exact prime_t64_223
      · exact prime_thirtyTwoAD_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 439297513) ^ 219648756 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 439297513) ^ 146432504 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 439297513) ^ 5560728 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 439297513) ^ 1969944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 439297513) ^ 422808 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_458069939 : Nat.Prime 458069939 := by
  apply lucas_primality 458069939 (2 : ZMod 458069939)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2801, 1), (81769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2801, 1), (81769, 1)] : List FactorBlock).map factorBlockValue).prod) = 458069939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_2801
      · exact prime_thirtyTwoAD_81769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 458069939) ^ 229034969 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 458069939) ^ 163538 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 458069939) ^ 5602 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_523703249 : Nat.Prime 523703249 := by
  apply lucas_primality 523703249 (3 : ZMod 523703249)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (32731453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (32731453, 1)] : List FactorBlock).map factorBlockValue).prod) = 523703249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_32731453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 523703249) ^ 261851624 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 523703249) ^ 16 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_539553341 : Nat.Prime 539553341 := by
  apply lucas_primality 539553341 (2 : ZMod 539553341)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (26977667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (26977667, 1)] : List FactorBlock).map factorBlockValue).prod) = 539553341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_26977667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 539553341) ^ 269776670 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 539553341) ^ 107910668 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 539553341) ^ 20 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_642191821 : Nat.Prime 642191821 := by
  apply lucas_primality 642191821 (2 : ZMod 642191821)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (167, 1), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) = 642191821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_167
      · exact prime_thirtyTwoAD_64091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642191821) ^ 321095910 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 214063940 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 128438364 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 3845460 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 642191821) ^ 10020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_672203149 : Nat.Prime 672203149 := by
  apply lucas_primality 672203149 (2 : ZMod 672203149)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (56016929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (56016929, 1)] : List FactorBlock).map factorBlockValue).prod) = 672203149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_56016929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 672203149) ^ 336101574 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 672203149) ^ 224067716 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 672203149) ^ 12 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_871363393 : Nat.Prime 871363393 := by
  apply lucas_primality 871363393 (5 : ZMod 871363393)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (191, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (191, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) = 871363393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_191
      · exact prime_thirtyTwoAD_23761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 871363393) ^ 435681696 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 871363393) ^ 290454464 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 871363393) ^ 4562112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 871363393) ^ 36672 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_930659839 : Nat.Prime 930659839 := by
  apply lucas_primality 930659839 (3 : ZMod 930659839)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (576617, 1)] : List FactorBlock).map factorBlockValue).prod) = 930659839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_269
      · exact prime_thirtyTwoAD_576617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 930659839) ^ 465329919 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 310219946 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 3459702 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 930659839) ^ 1614 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1074681301 : Nat.Prime 1074681301 := by
  apply lucas_primality 1074681301 (6 : ZMod 1074681301)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (11, 1), (46523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (11, 1), (46523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074681301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_46523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1074681301) ^ 537340650 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 1074681301) ^ 358227100 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 1074681301) ^ 214936260 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 1074681301) ^ 153525900 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 1074681301) ^ 97698300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 1074681301) ^ 23100 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1088621057 : Nat.Prime 1088621057 := by
  apply lucas_primality 1088621057 (3 : ZMod 1088621057)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088621057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_2126213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1088621057) ^ 544310528 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1088621057) ^ 512 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1254465811 : Nat.Prime 1254465811 := by
  apply lucas_primality 1254465811 (2 : ZMod 1254465811)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (659, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (659, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) = 1254465811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_659
      · exact prime_thirtyTwoAD_1627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1254465811) ^ 627232905 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1254465811) ^ 418155270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1254465811) ^ 250893162 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1254465811) ^ 96497370 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1254465811) ^ 1903590 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1254465811) ^ 771030 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_thirtyTwoAD_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1440916409 : Nat.Prime 1440916409 := by
  apply lucas_primality 1440916409 (3 : ZMod 1440916409)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (89, 1), (34301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440916409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_89
      · exact prime_thirtyTwoAD_34301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1440916409) ^ 720458204 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 24422312 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 16190072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440916409) ^ 42008 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1458322139 : Nat.Prime 1458322139 := by
  apply lucas_primality 1458322139 (2 : ZMod 1458322139)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (89, 1), (90031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (89, 1), (90031, 1)] : List FactorBlock).map factorBlockValue).prod) = 1458322139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_89
      · exact prime_thirtyTwoAD_90031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1458322139) ^ 729161069 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 208331734 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 112178626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 16385642 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458322139) ^ 16198 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1579816097 : Nat.Prime 1579816097 := by
  apply lucas_primality 1579816097 (3 : ZMod 1579816097)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (59, 1), (457, 1), (1831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (59, 1), (457, 1), (1831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579816097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_thirtyTwoAD_457
      · exact prime_thirtyTwoAD_1831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1579816097) ^ 789908048 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579816097) ^ 26776544 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579816097) ^ 3456928 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579816097) ^ 862816 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1596046247 : Nat.Prime 1596046247 := by
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1596046247) ^ 798023123 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 84002434 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 38 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1656564227 : Nat.Prime 1656564227 := by
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_2521
      · exact prime_thirtyTwoAD_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1656564227) ^ 828282113 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 16401626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 657106 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 509242 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1699732763 : Nat.Prime 1699732763 := by
  apply lucas_primality 1699732763 (5 : ZMod 1699732763)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (9339191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (9339191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1699732763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_9339191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1699732763) ^ 849866381 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699732763) ^ 242818966 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699732763) ^ 130748674 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699732763) ^ 182 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2026194593 : Nat.Prime 2026194593 := by
  apply lucas_primality 2026194593 (3 : ZMod 2026194593)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (71, 1), (24103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (71, 1), (24103, 1)] : List FactorBlock).map factorBlockValue).prod) = 2026194593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_24103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2026194593) ^ 1013097296 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2026194593) ^ 54762016 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2026194593) ^ 28537952 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2026194593) ^ 84064 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2399393959 : Nat.Prime 2399393959 := by
  apply lucas_primality 2399393959 (3 : ZMod 2399393959)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (659, 1), (46679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (659, 1), (46679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2399393959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_659
      · exact prime_thirtyTwoAD_46679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2399393959) ^ 1199696979 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2399393959) ^ 799797986 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2399393959) ^ 184568766 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2399393959) ^ 3640962 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 2399393959) ^ 51402 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2548927123 : Nat.Prime 2548927123 := by
  apply lucas_primality 2548927123 (2 : ZMod 2548927123)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (71, 1), (854771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (71, 1), (854771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2548927123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_854771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2548927123) ^ 1274463561 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 849642374 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 364132446 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 35900382 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2548927123) ^ 2982 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2713202621 : Nat.Prime 2713202621 := by
  apply lucas_primality 2713202621 (2 : ZMod 2713202621)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (135660131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (135660131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2713202621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_135660131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2713202621) ^ 1356601310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2713202621) ^ 542640524 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2713202621) ^ 20 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2935654901 : Nat.Prime 2935654901 := by
  apply lucas_primality 2935654901 (2 : ZMod 2935654901)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (293, 1), (100193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (293, 1), (100193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2935654901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_293
      · exact prime_thirtyTwoAD_100193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2935654901) ^ 1467827450 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935654901) ^ 587130980 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935654901) ^ 10019300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935654901) ^ 29300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2958879449 : Nat.Prime 2958879449 := by
  apply lucas_primality 2958879449 (6 : ZMod 2958879449)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (52837133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (52837133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2958879449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_52837133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2958879449) ^ 1479439724 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2958879449) ^ 422697064 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2958879449) ^ 56 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3233048479 : Nat.Prime 3233048479 := by
  apply lucas_primality 3233048479 (3 : ZMod 3233048479)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (137, 1), (357559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (137, 1), (357559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3233048479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_137
      · exact prime_thirtyTwoAD_357559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3233048479) ^ 1616524239 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3233048479) ^ 1077682826 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3233048479) ^ 293913498 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3233048479) ^ 23598894 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3233048479) ^ 9042 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3356083597 : Nat.Prime 3356083597 := by
  apply lucas_primality 3356083597 (2 : ZMod 3356083597)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (5276861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (5276861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3356083597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_thirtyTwoAD_5276861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3356083597) ^ 1678041798 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3356083597) ^ 1118694532 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3356083597) ^ 63322332 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3356083597) ^ 636 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3640375391 : Nat.Prime 3640375391 := by
  apply lucas_primality 3640375391 (7 : ZMod 3640375391)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (364037539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (364037539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3640375391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_364037539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3640375391) ^ 1820187695 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 3640375391) ^ 728075078 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 3640375391) ^ 10 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3928157339 : Nat.Prime 3928157339 := by
  apply lucas_primality 3928157339 (2 : ZMod 3928157339)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (67, 1), (4187801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (67, 1), (4187801, 1)] : List FactorBlock).map factorBlockValue).prod) = 3928157339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_4187801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3928157339) ^ 1964078669 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3928157339) ^ 561165334 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3928157339) ^ 58629214 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3928157339) ^ 938 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_5411288681 : Nat.Prime 5411288681 := by
  apply lucas_primality 5411288681 (3 : ZMod 5411288681)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (241, 1), (80191, 1)] : List FactorBlock).map factorBlockValue).prod) = 5411288681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_241
      · exact prime_thirtyTwoAD_80191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5411288681) ^ 2705644340 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 1082257736 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 773041240 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 22453480 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5411288681) ^ 67480 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_6557135309 : Nat.Prime 6557135309 := by
  apply lucas_primality 6557135309 (2 : ZMod 6557135309)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (12513617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (12513617, 1)] : List FactorBlock).map factorBlockValue).prod) = 6557135309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_131
      · exact prime_thirtyTwoAD_12513617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6557135309) ^ 3278567654 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 6557135309) ^ 50054468 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 6557135309) ^ 524 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_7062967943 : Nat.Prime 7062967943 := by
  apply lucas_primality 7062967943 (5 : ZMod 7062967943)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod) = 7062967943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_5479
      · exact prime_thirtyTwoAD_644549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7062967943) ^ 3531483971 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 1289098 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 10958 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_7647016217 : Nat.Prime 7647016217 := by
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_7549
      · exact prime_thirtyTwoAD_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7647016217) ^ 3823508108 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1092430888 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1012984 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 422744 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_8784511289 : Nat.Prime 8784511289 := by
  apply lucas_primality 8784511289 (3 : ZMod 8784511289)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (53, 1), (167, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8784511289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_t64_53
      · exact prime_t64_167
      · exact prime_t64_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8784511289) ^ 4392255644 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 1254930184 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 237419224 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 165745496 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 52601864 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8784511289) ^ 18339272 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_10892708831 : Nat.Prime 10892708831 := by
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod) = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_thirtyTwoAD_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10892708831) ^ 5446354415 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 2178541766 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 253318810 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 430 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_11527331273 : Nat.Prime 11527331273 := by
  apply lucas_primality 11527331273 (3 : ZMod 11527331273)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1440916409, 1)] : List FactorBlock).map factorBlockValue).prod) = 11527331273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_1440916409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11527331273) ^ 5763665636 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 11527331273) ^ 8 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_11981667823 : Nat.Prime 11981667823 := by
  apply lucas_primality 11981667823 (5 : ZMod 11981667823)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (149, 1), (122957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (149, 1), (122957, 1)] : List FactorBlock).map factorBlockValue).prod) = 11981667823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_109
      · exact prime_t64_149
      · exact prime_thirtyTwoAD_122957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11981667823) ^ 5990833911 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11981667823) ^ 3993889274 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11981667823) ^ 109923558 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11981667823) ^ 80413878 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11981667823) ^ 97446 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_12932193917 : Nat.Prime 12932193917 := by
  apply lucas_primality 12932193917 (2 : ZMod 12932193917)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3233048479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3233048479, 1)] : List FactorBlock).map factorBlockValue).prod) = 12932193917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_3233048479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12932193917) ^ 6466096958 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 12932193917) ^ 4 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_13053027349 : Nat.Prime 13053027349 := by
  apply lucas_primality 13053027349 (2 : ZMod 13053027349)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1511, 1), (239963, 1)] : List FactorBlock).map factorBlockValue).prod) = 13053027349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1511
      · exact prime_thirtyTwoAD_239963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13053027349) ^ 6526513674 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 4351009116 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 8638668 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13053027349) ^ 54396 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_14737656217 : Nat.Prime 14737656217 := by
  apply lucas_primality 14737656217 (10 : ZMod 14737656217)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4129, 1), (148721, 1)] : List FactorBlock).map factorBlockValue).prod) = 14737656217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_4129
      · exact prime_thirtyTwoAD_148721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 14737656217) ^ 7368828108 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 4912552072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 3569304 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 14737656217) ^ 99096 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_15040590709 : Nat.Prime 15040590709 := by
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod) = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_311
      · exact prime_thirtyTwoAD_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15040590709) ^ 7520295354 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 5013530236 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1367326428 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1156968516 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 48362028 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 533676 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_18033052153 : Nat.Prime 18033052153 := by
  apply lucas_primality 18033052153 (5 : ZMod 18033052153)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (443, 1), (89269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (443, 1), (89269, 1)] : List FactorBlock).map factorBlockValue).prod) = 18033052153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_443
      · exact prime_thirtyTwoAD_89269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18033052153) ^ 9016526076 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18033052153) ^ 6011017384 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18033052153) ^ 949108008 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18033052153) ^ 40706664 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 18033052153) ^ 202008 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_19277900387 : Nat.Prime 19277900387 := by
  apply lucas_primality 19277900387 (2 : ZMod 19277900387)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (419084791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (419084791, 1)] : List FactorBlock).map factorBlockValue).prod) = 19277900387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_419084791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19277900387) ^ 9638950193 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 19277900387) ^ 838169582 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 19277900387) ^ 46 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_20785154287 : Nat.Prime 20785154287 := by
  apply lucas_primality 20785154287 (3 : ZMod 20785154287)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (266476337, 1)] : List FactorBlock).map factorBlockValue).prod) = 20785154287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_266476337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20785154287) ^ 10392577143 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 6928384762 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 1598858022 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 20785154287) ^ 78 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_22457615119 : Nat.Prime 22457615119 := by
  apply lucas_primality 22457615119 (3 : ZMod 22457615119)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1613, 1), (2320481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1613, 1), (2320481, 1)] : List FactorBlock).map factorBlockValue).prod) = 22457615119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1613
      · exact prime_thirtyTwoAD_2320481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22457615119) ^ 11228807559 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 22457615119) ^ 7485871706 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 22457615119) ^ 13922886 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 22457615119) ^ 9678 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_23959559521 : Nat.Prime 23959559521 := by
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_191
      · exact prime_thirtyTwoAD_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23959559521) ^ 11979779760 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 7986519840 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 4791911904 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 1843043040 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 125442720 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 3575520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_26620044299 : Nat.Prime 26620044299 := by
  apply lucas_primality 26620044299 (2 : ZMod 26620044299)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (67, 1), (6850243, 1)] : List FactorBlock).map factorBlockValue).prod) = 26620044299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_6850243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26620044299) ^ 13310022149 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 917932562 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 397314094 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 26620044299) ^ 3886 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_29217258659 : Nat.Prime 29217258659 := by
  apply lucas_primality 29217258659 (6 : ZMod 29217258659)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (122761591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (122761591, 1)] : List FactorBlock).map factorBlockValue).prod) = 29217258659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_122761591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 29217258659) ^ 14608629329 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 29217258659) ^ 4173894094 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 29217258659) ^ 1718662274 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 29217258659) ^ 238 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_38540602237 : Nat.Prime 38540602237 := by
  apply lucas_primality 38540602237 (2 : ZMod 38540602237)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (110748857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (110748857, 1)] : List FactorBlock).map factorBlockValue).prod) = 38540602237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_thirtyTwoAD_110748857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38540602237) ^ 19270301118 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 38540602237) ^ 12846867412 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 38540602237) ^ 1328986284 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 38540602237) ^ 348 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_40548411623 : Nat.Prime 40548411623 := by
  apply lucas_primality 40548411623 (5 : ZMod 40548411623)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (200734711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (200734711, 1)] : List FactorBlock).map factorBlockValue).prod) = 40548411623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_200734711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40548411623) ^ 20274205811 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 40548411623) ^ 401469422 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 40548411623) ^ 202 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_51966456109 : Nat.Prime 51966456109 := by
  apply lucas_primality 51966456109 (14 : ZMod 51966456109)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (307, 1), (2015141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (307, 1), (2015141, 1)] : List FactorBlock).map factorBlockValue).prod) = 51966456109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_307
      · exact prime_thirtyTwoAD_2015141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 51966456109) ^ 25983228054 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 51966456109) ^ 17322152036 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 51966456109) ^ 7423779444 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 51966456109) ^ 169271844 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 51966456109) ^ 25788 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_54675980063 : Nat.Prime 54675980063 := by
  apply lucas_primality 54675980063 (5 : ZMod 54675980063)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (197, 1), (206813, 1)] : List FactorBlock).map factorBlockValue).prod) = 54675980063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_61
      · exact prime_t64_197
      · exact prime_thirtyTwoAD_206813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54675980063) ^ 27337990031 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 4970543642 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 896327542 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 277543046 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 54675980063) ^ 264374 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_60083373169 : Nat.Prime 60083373169 := by
  apply lucas_primality 60083373169 (11 : ZMod 60083373169)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (13, 1), (31, 1), (353, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 60083373169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_thirtyTwoAD_353
      · exact prime_thirtyTwoAD_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 60083373169) ^ 30041686584 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 20027791056 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 8583339024 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 4621797936 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 1938173328 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 170207856 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 60083373169) ^ 143397072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_67242746707 : Nat.Prime 67242746707 := by
  apply lucas_primality 67242746707 (5 : ZMod 67242746707)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6833, 1), (1640147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6833, 1), (1640147, 1)] : List FactorBlock).map factorBlockValue).prod) = 67242746707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_6833
      · exact prime_thirtyTwoAD_1640147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67242746707) ^ 33621373353 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 67242746707) ^ 22414248902 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 67242746707) ^ 9840882 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 67242746707) ^ 40998 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_76085543257 : Nat.Prime 76085543257 := by
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod) = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_2221
      · exact prime_thirtyTwoAD_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76085543257) ^ 38042771628 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 25361847752 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 34257336 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 53304 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_78749395507 : Nat.Prime 78749395507 := by
  apply lucas_primality 78749395507 (2 : ZMod 78749395507)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1458322139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1458322139, 1)] : List FactorBlock).map factorBlockValue).prod) = 78749395507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1458322139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78749395507) ^ 39374697753 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 78749395507) ^ 26249798502 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 78749395507) ^ 54 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_107468130101 : Nat.Prime 107468130101 := by
  apply lucas_primality 107468130101 (2 : ZMod 107468130101)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (1074681301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (1074681301, 1)] : List FactorBlock).map factorBlockValue).prod) = 107468130101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_1074681301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107468130101) ^ 53734065050 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 107468130101) ^ 21493626020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 107468130101) ^ 100 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_108683062133 : Nat.Prime 108683062133 := by
  apply lucas_primality 108683062133 (2 : ZMod 108683062133)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82889, 1), (327797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82889, 1), (327797, 1)] : List FactorBlock).map factorBlockValue).prod) = 108683062133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_82889
      · exact prime_thirtyTwoAD_327797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108683062133) ^ 54341531066 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 108683062133) ^ 1311188 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 108683062133) ^ 331556 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_132501777739 : Nat.Prime 132501777739 := by
  apply lucas_primality 132501777739 (3 : ZMod 132501777739)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (8747, 1), (229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 132501777739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_8747
      · exact prime_thirtyTwoAD_229519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132501777739) ^ 66250888869 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 44167259246 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 12045616158 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 15148254 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 132501777739) ^ 577302 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_135031325183 : Nat.Prime 135031325183 := by
  apply lucas_primality 135031325183 (5 : ZMod 135031325183)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (449, 1), (11566843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (449, 1), (11566843, 1)] : List FactorBlock).map factorBlockValue).prod) = 135031325183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_449
      · exact prime_thirtyTwoAD_11566843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 135031325183) ^ 67515662591 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 10387025014 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 300737918 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 135031325183) ^ 11674 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_152895766423 : Nat.Prime 152895766423 := by
  apply lucas_primality 152895766423 (3 : ZMod 152895766423)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3640375391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3640375391, 1)] : List FactorBlock).map factorBlockValue).prod) = 152895766423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_3640375391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152895766423) ^ 76447883211 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 50965255474 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 21842252346 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 152895766423) ^ 42 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_159097227851 : Nat.Prime 159097227851 := by
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod) = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159097227851) ^ 79548613925 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 31819445570 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 14463384350 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 550 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_166031598869 : Nat.Prime 166031598869 := by
  apply lucas_primality 166031598869 (2 : ZMod 166031598869)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (479, 1), (677, 1), (4129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (479, 1), (677, 1), (4129, 1)] : List FactorBlock).map factorBlockValue).prod) = 166031598869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_479
      · exact prime_thirtyTwoAD_677
      · exact prime_thirtyTwoAD_4129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 166031598869) ^ 83015799434 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 166031598869) ^ 5355858028 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 166031598869) ^ 346621292 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 166031598869) ^ 245246084 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 166031598869) ^ 40211092 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_180623862983 : Nat.Prime 180623862983 := by
  apply lucas_primality 180623862983 (5 : ZMod 180623862983)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (8273, 1), (474629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (8273, 1), (474629, 1)] : List FactorBlock).map factorBlockValue).prod) = 180623862983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_8273
      · exact prime_thirtyTwoAD_474629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 180623862983) ^ 90311931491 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 180623862983) ^ 7853211434 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 180623862983) ^ 21832934 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 180623862983) ^ 380558 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_205248987289 : Nat.Prime 205248987289 := by
  apply lucas_primality 205248987289 (7 : ZMod 205248987289)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (109, 1), (8717677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (109, 1), (8717677, 1)] : List FactorBlock).map factorBlockValue).prod) = 205248987289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_109
      · exact prime_thirtyTwoAD_8717677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 205248987289) ^ 102624493644 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 205248987289) ^ 68416329096 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 205248987289) ^ 1883018232 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 205248987289) ^ 23544 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_205337438731 : Nat.Prime 205337438731 := by
  apply lucas_primality 205337438731 (2 : ZMod 205337438731)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (811, 1), (2813227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (811, 1), (2813227, 1)] : List FactorBlock).map factorBlockValue).prod) = 205337438731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_811
      · exact prime_thirtyTwoAD_2813227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 205337438731) ^ 102668719365 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 205337438731) ^ 68445812910 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 205337438731) ^ 41067487746 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 205337438731) ^ 253190430 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 205337438731) ^ 72990 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_206997240473 : Nat.Prime 206997240473 := by
  apply lucas_primality 206997240473 (3 : ZMod 206997240473)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1201, 1), (1958569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1201, 1), (1958569, 1)] : List FactorBlock).map factorBlockValue).prod) = 206997240473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_1201
      · exact prime_thirtyTwoAD_1958569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 206997240473) ^ 103498620236 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 206997240473) ^ 18817930952 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 206997240473) ^ 172354072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 206997240473) ^ 105688 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_211883927903 : Nat.Prime 211883927903 := by
  apply lucas_primality 211883927903 (5 : ZMod 211883927903)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (36457, 1), (78539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (36457, 1), (78539, 1)] : List FactorBlock).map factorBlockValue).prod) = 211883927903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_36457
      · exact prime_thirtyTwoAD_78539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 211883927903) ^ 105941963951 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 211883927903) ^ 5726592646 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 211883927903) ^ 5811886 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 211883927903) ^ 2697818 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_229440973631 : Nat.Prime 229440973631 := by
  apply lucas_primality 229440973631 (14 : ZMod 229440973631)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (31, 1), (691, 1), (97373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (31, 1), (691, 1), (97373, 1)] : List FactorBlock).map factorBlockValue).prod) = 229440973631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_31
      · exact prime_thirtyTwoAD_691
      · exact prime_thirtyTwoAD_97373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 229440973631) ^ 114720486815 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 229440973631) ^ 45888194726 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 229440973631) ^ 20858270330 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 229440973631) ^ 7401321730 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 229440973631) ^ 332041930 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (14 : ZMod 229440973631) ^ 2356310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_270502052749 : Nat.Prime 270502052749 := by
  apply lucas_primality 270502052749 (2 : ZMod 270502052749)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (163, 1), (2609311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (163, 1), (2609311, 1)] : List FactorBlock).map factorBlockValue).prod) = 270502052749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_t64_163
      · exact prime_thirtyTwoAD_2609311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 270502052749) ^ 135251026374 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 270502052749) ^ 90167350916 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 270502052749) ^ 5103812316 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 270502052749) ^ 1659521796 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 270502052749) ^ 103668 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_316001240129 : Nat.Prime 316001240129 := by
  apply lucas_primality 316001240129 (3 : ZMod 316001240129)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (3499, 1), (201589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (3499, 1), (201589, 1)] : List FactorBlock).map factorBlockValue).prod) = 316001240129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_3499
      · exact prime_thirtyTwoAD_201589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 316001240129) ^ 158000620064 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 316001240129) ^ 45143034304 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 316001240129) ^ 90311872 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 316001240129) ^ 1567552 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_344256547937 : Nat.Prime 344256547937 := by
  apply lucas_primality 344256547937 (3 : ZMod 344256547937)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2467, 1), (622967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2467, 1), (622967, 1)] : List FactorBlock).map factorBlockValue).prod) = 344256547937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_2467
      · exact prime_thirtyTwoAD_622967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 344256547937) ^ 172128273968 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 49179506848 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 139544608 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 344256547937) ^ 552608 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_348963959107 : Nat.Prime 348963959107 := by
  apply lucas_primality 348963959107 (2 : ZMod 348963959107)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (149, 1), (271, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (149, 1), (271, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) = 348963959107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_149
      · exact prime_thirtyTwoAD_271
      · exact prime_thirtyTwoAD_7621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 348963959107) ^ 174481979553 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 348963959107) ^ 116321319702 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 348963959107) ^ 49851994158 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 348963959107) ^ 2342039994 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 348963959107) ^ 1287689886 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 348963959107) ^ 45789786 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_390056504429 : Nat.Prime 390056504429 := by
  apply lucas_primality 390056504429 (2 : ZMod 390056504429)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod) = 390056504429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_677
      · exact prime_thirtyTwoAD_144038591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390056504429) ^ 195028252214 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 576154364 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 2708 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_413994480947 : Nat.Prime 413994480947 := by
  apply lucas_primality 413994480947 (2 : ZMod 413994480947)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (206997240473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (206997240473, 1)] : List FactorBlock).map factorBlockValue).prod) = 413994480947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_206997240473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 413994480947) ^ 206997240473 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 413994480947) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_458881947263 : Nat.Prime 458881947263 := by
  apply lucas_primality 458881947263 (5 : ZMod 458881947263)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229440973631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229440973631, 1)] : List FactorBlock).map factorBlockValue).prod) = 458881947263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_229440973631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 458881947263) ^ 229440973631 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 458881947263) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_763558914047 : Nat.Prime 763558914047 := by
  apply lucas_primality 763558914047 (5 : ZMod 763558914047)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (22457615119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (22457615119, 1)] : List FactorBlock).map factorBlockValue).prod) = 763558914047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_22457615119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 763558914047) ^ 381779457023 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 763558914047) ^ 44915230238 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 763558914047) ^ 34 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_845468611489 : Nat.Prime 845468611489 := by
  apply lucas_primality 845468611489 (7 : ZMod 845468611489)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (2935654901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (2935654901, 1)] : List FactorBlock).map factorBlockValue).prod) = 845468611489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_2935654901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 845468611489) ^ 422734305744 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 845468611489) ^ 281822870496 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 845468611489) ^ 288 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_925339218577 : Nat.Prime 925339218577 := by
  apply lucas_primality 925339218577 (5 : ZMod 925339218577)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19277900387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19277900387, 1)] : List FactorBlock).map factorBlockValue).prod) = 925339218577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_19277900387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 925339218577) ^ 462669609288 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 925339218577) ^ 308446406192 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 925339218577) ^ 48 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1272241326337 : Nat.Prime 1272241326337 := by
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1272241326337) ^ 636120663168 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 424080442112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 768 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1312486028963 : Nat.Prime 1312486028963 := by
  apply lucas_primality 1312486028963 (2 : ZMod 1312486028963)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7541, 1), (87023341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7541, 1), (87023341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1312486028963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_7541
      · exact prime_thirtyTwoAD_87023341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1312486028963) ^ 656243014481 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312486028963) ^ 174046682 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312486028963) ^ 15082 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1669603069061 : Nat.Prime 1669603069061 := by
  apply lucas_primality 1669603069061 (2 : ZMod 1669603069061)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (15803, 1), (278029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (15803, 1), (278029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1669603069061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_15803
      · exact prime_thirtyTwoAD_278029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1669603069061) ^ 834801534530 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1669603069061) ^ 333920613812 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1669603069061) ^ 87873845740 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1669603069061) ^ 105651020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1669603069061) ^ 6005140 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1932735268463 : Nat.Prime 1932735268463 := by
  apply lucas_primality 1932735268463 (5 : ZMod 1932735268463)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (373, 2), (301993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (373, 2), (301993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932735268463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_373
      · exact prime_thirtyTwoAD_301993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1932735268463) ^ 966367634231 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1932735268463) ^ 84031968194 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1932735268463) ^ 5181595894 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1932735268463) ^ 6399934 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1982473007243 : Nat.Prime 1982473007243 := by
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1982473007243) ^ 991236503621 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 283210429606 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 152497923634 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 182 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_9739
      · exact prime_thirtyTwoAD_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2196123429911 : Nat.Prime 2196123429911 := by
  apply lucas_primality 2196123429911 (11 : ZMod 2196123429911)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1487, 1), (147688193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1487, 1), (147688193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2196123429911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_1487
      · exact prime_thirtyTwoAD_147688193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2196123429911) ^ 1098061714955 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2196123429911) ^ 439224685982 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2196123429911) ^ 1476881930 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2196123429911) ^ 14870 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2329141311671 : Nat.Prime 2329141311671 := by
  apply lucas_primality 2329141311671 (11 : ZMod 2329141311671)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (5413, 1), (402137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329141311671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_thirtyTwoAD_5413
      · exact prime_thirtyTwoAD_402137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2329141311671) ^ 1164570655835 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 465828262334 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 21767675810 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 430286590 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (11 : ZMod 2329141311671) ^ 5791910 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3220080991709 : Nat.Prime 3220080991709 := by
  apply lucas_primality 3220080991709 (3 : ZMod 3220080991709)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (19, 1), (67, 1), (5314121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (19, 1), (67, 1), (5314121, 1)] : List FactorBlock).map factorBlockValue).prod) = 3220080991709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_5314121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3220080991709) ^ 1610040495854 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3220080991709) ^ 460011570244 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3220080991709) ^ 189416528924 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3220080991709) ^ 169477946932 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3220080991709) ^ 48060910324 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3220080991709) ^ 605948 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3320631977381 : Nat.Prime 3320631977381 := by
  apply lucas_primality 3320631977381 (2 : ZMod 3320631977381)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (166031598869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (166031598869, 1)] : List FactorBlock).map factorBlockValue).prod) = 3320631977381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_166031598869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3320631977381) ^ 1660315988690 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3320631977381) ^ 664126395476 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3320631977381) ^ 20 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_4287731098507 : Nat.Prime 4287731098507 := by
  apply lucas_primality 4287731098507 (2 : ZMod 4287731098507)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (167, 1), (70150373, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287731098507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_t64_167
      · exact prime_thirtyTwoAD_70150373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4287731098507) ^ 2143865549253 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 1429243699502 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 70290673746 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 25675036518 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287731098507) ^ 61122 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_4392246859823 : Nat.Prime 4392246859823 := by
  apply lucas_primality 4392246859823 (5 : ZMod 4392246859823)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2196123429911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2196123429911, 1)] : List FactorBlock).map factorBlockValue).prod) = 4392246859823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_2196123429911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4392246859823) ^ 2196123429911 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 4392246859823) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_4658282623343 : Nat.Prime 4658282623343 := by
  apply lucas_primality 4658282623343 (5 : ZMod 4658282623343)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2329141311671, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658282623343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_2329141311671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4658282623343) ^ 2329141311671 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 4658282623343) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_5639275250353 : Nat.Prime 5639275250353 := by
  apply lucas_primality 5639275250353 (5 : ZMod 5639275250353)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (123701, 1), (316583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (123701, 1), (316583, 1)] : List FactorBlock).map factorBlockValue).prod) = 5639275250353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_123701
      · exact prime_thirtyTwoAD_316583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5639275250353) ^ 2819637625176 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639275250353) ^ 1879758416784 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639275250353) ^ 45587952 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639275250353) ^ 17812944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_5934672374047 : Nat.Prime 5934672374047 := by
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934672374047) ^ 2967336187023 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 1978224124682 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 456513259542 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 78 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_6294849896641 : Nat.Prime 6294849896641 := by
  apply lucas_primality 6294849896641 (7 : ZMod 6294849896641)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (6557135309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (6557135309, 1)] : List FactorBlock).map factorBlockValue).prod) = 6294849896641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_6557135309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6294849896641) ^ 3147424948320 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 6294849896641) ^ 2098283298880 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 6294849896641) ^ 1258969979328 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 6294849896641) ^ 960 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_8215068638333 : Nat.Prime 8215068638333 := by
  apply lucas_primality 8215068638333 (2 : ZMod 8215068638333)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (937, 1), (75581171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (937, 1), (75581171, 1)] : List FactorBlock).map factorBlockValue).prod) = 8215068638333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_thirtyTwoAD_937
      · exact prime_thirtyTwoAD_75581171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8215068638333) ^ 4107534319166 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 283278228908 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 8767415836 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8215068638333) ^ 108692 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_8402550447737 : Nat.Prime 8402550447737 := by
  apply lucas_primality 8402550447737 (3 : ZMod 8402550447737)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (381761, 1), (2751247, 1)] : List FactorBlock).map factorBlockValue).prod) = 8402550447737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_381761
      · exact prime_thirtyTwoAD_2751247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8402550447737) ^ 4201275223868 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 22009976 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 8402550447737) ^ 3054088 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_10185255900343 : Nat.Prime 10185255900343 := by
  apply lucas_primality 10185255900343 (3 : ZMod 10185255900343)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (59, 1), (10909, 1), (46271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (59, 1), (10909, 1), (46271, 1)] : List FactorBlock).map factorBlockValue).prod) = 10185255900343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_59
      · exact prime_thirtyTwoAD_10909
      · exact prime_thirtyTwoAD_46271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10185255900343) ^ 5092627950171 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 10185255900343) ^ 3395085300114 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 10185255900343) ^ 536066100018 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 10185255900343) ^ 172631455938 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 10185255900343) ^ 933656238 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 10185255900343) ^ 220121802 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_11012157741281 : Nat.Prime 11012157741281 := by
  apply lucas_primality 11012157741281 (3 : ZMod 11012157741281)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (31, 1), (137, 1), (16205789, 1)] : List FactorBlock).map factorBlockValue).prod) = 11012157741281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_t64_137
      · exact prime_thirtyTwoAD_16205789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11012157741281) ^ 5506078870640 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 2202431548256 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 355230894880 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 80380713440 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 11012157741281) ^ 679520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_11680677399577 : Nat.Prime 11680677399577 := by
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_79
      · exact prime_thirtyTwoAD_397
      · exact prime_thirtyTwoAD_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11680677399577) ^ 5840338699788 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 3893559133192 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 507855539112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 147856675944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 29422361208 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 17312376 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_12550654586551 : Nat.Prime 12550654586551 := by
  apply lucas_primality 12550654586551 (6 : ZMod 12550654586551)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (66553, 1), (1257209, 1)] : List FactorBlock).map factorBlockValue).prod) = 12550654586551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_66553
      · exact prime_thirtyTwoAD_1257209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12550654586551) ^ 6275327293275 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 4183551528850 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 2510130917310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 188581350 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 12550654586551) ^ 9982950 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_13424731660273 : Nat.Prime 13424731660273 := by
  apply lucas_primality 13424731660273 (5 : ZMod 13424731660273)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (379, 1), (907, 1), (813613, 1)] : List FactorBlock).map factorBlockValue).prod) = 13424731660273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_379
      · exact prime_thirtyTwoAD_907
      · exact prime_thirtyTwoAD_813613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13424731660273) ^ 6712365830136 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 4474910553424 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 35421455568 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 14801247696 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 13424731660273) ^ 16500144 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_13443454509487 : Nat.Prime 13443454509487 := by
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_293
      · exact prime_thirtyTwoAD_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13443454509487) ^ 6721727254743 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 4481151503162 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 45882097302 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 1758 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_17883389214479 : Nat.Prime 17883389214479 := by
  apply lucas_primality 17883389214479 (19 : ZMod 17883389214479)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1459457, 1), (6126727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1459457, 1), (6126727, 1)] : List FactorBlock).map factorBlockValue).prod) = 17883389214479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_1459457
      · exact prime_thirtyTwoAD_6126727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 17883389214479) ^ 8941694607239 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (19 : ZMod 17883389214479) ^ 12253454 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (19 : ZMod 17883389214479) ^ 2918914 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_45820001621089 : Nat.Prime 45820001621089 := by
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod) = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 45820001621089) ^ 22910000810544 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 15273333873696 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 288 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_thirtyTwoAD_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_74050722409721 : Nat.Prime 74050722409721 := by
  apply lucas_primality 74050722409721 (6 : ZMod 74050722409721)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (15131, 1), (17478479, 1)] : List FactorBlock).map factorBlockValue).prod) = 74050722409721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_15131
      · exact prime_thirtyTwoAD_17478479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74050722409721) ^ 37025361204860 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 14810144481944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 10578674629960 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4893974120 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 74050722409721) ^ 4236680 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_93633872061337 : Nat.Prime 93633872061337 := by
  apply lucas_primality 93633872061337 (5 : ZMod 93633872061337)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (205337438731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (205337438731, 1)] : List FactorBlock).map factorBlockValue).prod) = 93633872061337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_205337438731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 93633872061337) ^ 46816936030668 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 93633872061337) ^ 31211290687112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 93633872061337) ^ 4928098529544 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 93633872061337) ^ 456 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_98372345516581 : Nat.Prime 98372345516581 := by
  apply lucas_primality 98372345516581 (2 : ZMod 98372345516581)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod) = 98372345516581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_103393
      · exact prime_thirtyTwoAD_15857351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98372345516581) ^ 49186172758290 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 32790781838860 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 19674469103316 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 951441060 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 6203580 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_111480559507871 : Nat.Prime 111480559507871 := by
  apply lucas_primality 111480559507871 (7 : ZMod 111480559507871)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (59333, 1), (26841377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (59333, 1), (26841377, 1)] : List FactorBlock).map factorBlockValue).prod) = 111480559507871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_59333
      · exact prime_thirtyTwoAD_26841377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 111480559507871) ^ 55740279753935 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 111480559507871) ^ 22296111901574 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 111480559507871) ^ 15925794215410 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 111480559507871) ^ 1878896390 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 111480559507871) ^ 4153310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_128096483851537 : Nat.Prime 128096483851537 := by
  apply lucas_primality 128096483851537 (10 : ZMod 128096483851537)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (499, 1), (647, 1), (8265919, 1)] : List FactorBlock).map factorBlockValue).prod) = 128096483851537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_499
      · exact prime_t64_647
      · exact prime_thirtyTwoAD_8265919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 128096483851537) ^ 64048241925768 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 42698827950512 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 256706380464 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 197985291888 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 128096483851537) ^ 15496944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_154618821477041 : Nat.Prime 154618821477041 := by
  apply lucas_primality 154618821477041 (3 : ZMod 154618821477041)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1932735268463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1932735268463, 1)] : List FactorBlock).map factorBlockValue).prod) = 154618821477041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_1932735268463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 154618821477041) ^ 77309410738520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 154618821477041) ^ 30923764295408 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 154618821477041) ^ 80 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_167832428999197 : Nat.Prime 167832428999197 := by
  apply lucas_primality 167832428999197 (2 : ZMod 167832428999197)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (73, 1), (14737656217, 1)] : List FactorBlock).map factorBlockValue).prod) = 167832428999197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_73
      · exact prime_thirtyTwoAD_14737656217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167832428999197) ^ 83916214499598 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 55944142999732 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 12910186846092 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 2299074369852 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 167832428999197) ^ 11388 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_184337297790719 : Nat.Prime 184337297790719 := by
  apply lucas_primality 184337297790719 (13 : ZMod 184337297790719)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (2377, 1), (9043, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (2377, 1), (9043, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) = 184337297790719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_307
      · exact prime_t64_2377
      · exact prime_thirtyTwoAD_9043
      · exact prime_thirtyTwoAD_13967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 184337297790719) ^ 92168648895359 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 184337297790719) ^ 600447224074 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 184337297790719) ^ 77550398734 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 184337297790719) ^ 20384529226 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 184337297790719) ^ 13198059554 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_284731330549429 : Nat.Prime 284731330549429 := by
  apply lucas_primality 284731330549429 (2 : ZMod 284731330549429)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (67, 1), (4441, 1), (1265779, 1)] : List FactorBlock).map factorBlockValue).prod) = 284731330549429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_4441
      · exact prime_thirtyTwoAD_1265779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 284731330549429) ^ 142365665274714 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 94910443516476 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 40675904364204 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 4249721351484 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 64114237908 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 284731330549429) ^ 224945532 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_289817799176999 : Nat.Prime 289817799176999 := by
  apply lucas_primality 289817799176999 (7 : ZMod 289817799176999)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (439, 1), (5411288681, 1)] : List FactorBlock).map factorBlockValue).prod) = 289817799176999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_t64_439
      · exact prime_thirtyTwoAD_5411288681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 289817799176999) ^ 144908899588499 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 4751111461918 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 660177219082 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 289817799176999) ^ 53558 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_416726749916363 : Nat.Prime 416726749916363 := by
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod) = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_4787
      · exact prime_thirtyTwoAD_8839
      · exact prime_thirtyTwoAD_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416726749916363) ^ 208363374958181 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 87053843726 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 47146368358 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 84624586 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_522414067849459 : Nat.Prime 522414067849459 := by
  apply lucas_primality 522414067849459 (2 : ZMod 522414067849459)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (71, 1), (20785154287, 1)] : List FactorBlock).map factorBlockValue).prod) = 522414067849459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_20785154287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 522414067849459) ^ 261207033924729 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 174138022616486 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 8854475726262 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 7357944617598 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 522414067849459) ^ 25134 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_800697206514731 : Nat.Prime 800697206514731 := by
  apply lucas_primality 800697206514731 (2 : ZMod 800697206514731)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (59, 1), (499, 1), (388523879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (59, 1), (499, 1), (388523879, 1)] : List FactorBlock).map factorBlockValue).prod) = 800697206514731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_59
      · exact prime_t64_499
      · exact prime_thirtyTwoAD_388523879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 800697206514731) ^ 400348603257365 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 800697206514731) ^ 160139441302946 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 800697206514731) ^ 114385315216390 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 800697206514731) ^ 13571139093470 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 800697206514731) ^ 1604603620270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 800697206514731) ^ 2060870 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1276216592026469 : Nat.Prime 1276216592026469 := by
  apply lucas_primality 1276216592026469 (2 : ZMod 1276216592026469)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276216592026469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_293081
      · exact prime_thirtyTwoAD_1088621057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1276216592026469) ^ 638108296013234 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 4354484228 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 1172324 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1426018778793047 : Nat.Prime 1426018778793047 := by
  apply lucas_primality 1426018778793047 (5 : ZMod 1426018778793047)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11867, 1), (60083373169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426018778793047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_11867
      · exact prime_thirtyTwoAD_60083373169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1426018778793047) ^ 713009389396523 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 120166746338 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426018778793047) ^ 23734 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1569947948827553 : Nat.Prime 1569947948827553 := by
  apply lucas_primality 1569947948827553 (3 : ZMod 1569947948827553)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (89, 1), (78749395507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (89, 1), (78749395507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569947948827553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_thirtyTwoAD_78749395507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1569947948827553) ^ 784973974413776 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 224278278403936 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 17639864593568 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569947948827553) ^ 19936 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3132511198980767 : Nat.Prime 3132511198980767 := by
  apply lucas_primality 3132511198980767 (5 : ZMod 3132511198980767)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (3533, 1), (11981667823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (3533, 1), (11981667823, 1)] : List FactorBlock).map factorBlockValue).prod) = 3132511198980767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_thirtyTwoAD_3533
      · exact prime_thirtyTwoAD_11981667823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3132511198980767) ^ 1566255599490383 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 3132511198980767) ^ 84662464837318 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 3132511198980767) ^ 886643418902 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 3132511198980767) ^ 261442 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_8855378596144573 : Nat.Prime 8855378596144573 := by
  apply lucas_primality 8855378596144573 (2 : ZMod 8855378596144573)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (83, 1), (547, 1), (439297513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (83, 1), (547, 1), (439297513, 1)] : List FactorBlock).map factorBlockValue).prod) = 8855378596144573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_t64_83
      · exact prime_thirtyTwoAD_547
      · exact prime_thirtyTwoAD_439297513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8855378596144573) ^ 4427689298072286 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8855378596144573) ^ 2951792865381524 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8855378596144573) ^ 239334556652556 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8855378596144573) ^ 106691308387284 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8855378596144573) ^ 16188991949076 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8855378596144573) ^ 20158044 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_9661147067553533 : Nat.Prime 9661147067553533 := by
  apply lucas_primality 9661147067553533 (2 : ZMod 9661147067553533)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 2), (191, 1), (2026194593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 2), (191, 1), (2026194593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9661147067553533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_t64_191
      · exact prime_thirtyTwoAD_2026194593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9661147067553533) ^ 4830573533776766 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 9661147067553533) ^ 122293000855108 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 9661147067553533) ^ 50581921819652 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 9661147067553533) ^ 4768124 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_9691183070205617 : Nat.Prime 9691183070205617 := by
  apply lucas_primality 9691183070205617 (3 : ZMod 9691183070205617)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod) = 9691183070205617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_12251
      · exact prime_thirtyTwoAD_7062967943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9691183070205617) ^ 4845591535102808 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1384454724315088 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 791052409616 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1372112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_9866893336187777 : Nat.Prime 9866893336187777 := by
  apply lucas_primality 9866893336187777 (3 : ZMod 9866893336187777)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (11012157741281, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866893336187777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_11012157741281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9866893336187777) ^ 4933446668093888 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 1409556190883968 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 9866893336187777) ^ 896 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_384973
      · exact prime_thirtyTwoAD_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_21363163232632363 : Nat.Prime 21363163232632363 := by
  apply lucas_primality 21363163232632363 (3 : ZMod 21363163232632363)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (71, 1), (593, 1), (2003, 1), (611887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (71, 1), (593, 1), (2003, 1), (611887, 1)] : List FactorBlock).map factorBlockValue).prod) = 21363163232632363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_593
      · exact prime_thirtyTwoAD_2003
      · exact prime_thirtyTwoAD_611887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21363163232632363) ^ 10681581616316181 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 7121054410877454 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 928833184027494 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 300889622994822 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 36025570375434 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 10665583241454 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 21363163232632363) ^ 34913575926 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_28825099434530317 : Nat.Prime 28825099434530317 := by
  apply lucas_primality 28825099434530317 (2 : ZMod 28825099434530317)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (800697206514731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (800697206514731, 1)] : List FactorBlock).map factorBlockValue).prod) = 28825099434530317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_800697206514731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28825099434530317) ^ 14412549717265158 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 28825099434530317) ^ 9608366478176772 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 28825099434530317) ^ 36 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_30097468104848087 : Nat.Prime 30097468104848087 := by
  apply lucas_primality 30097468104848087 (5 : ZMod 30097468104848087)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (62596619, 1), (240408097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (62596619, 1), (240408097, 1)] : List FactorBlock).map factorBlockValue).prod) = 30097468104848087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_62596619
      · exact prime_thirtyTwoAD_240408097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30097468104848087) ^ 15048734052424043 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 30097468104848087) ^ 480816194 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 30097468104848087) ^ 125193238 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_33368908662535517 : Nat.Prime 33368908662535517 := by
  apply lucas_primality 33368908662535517 (2 : ZMod 33368908662535517)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (19, 1), (71, 1), (51966456109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (19, 1), (71, 1), (51966456109, 1)] : List FactorBlock).map factorBlockValue).prod) = 33368908662535517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_51966456109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33368908662535517) ^ 16684454331267758 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 33368908662535517) ^ 4766986951790788 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 33368908662535517) ^ 1962876980149148 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 33368908662535517) ^ 1756258350659764 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 33368908662535517) ^ 469984629049796 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 33368908662535517) ^ 642124 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_47026062802918237 : Nat.Prime 47026062802918237 := by
  apply lucas_primality 47026062802918237 (6 : ZMod 47026062802918237)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1217, 1), (3220080991709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1217, 1), (3220080991709, 1)] : List FactorBlock).map factorBlockValue).prod) = 47026062802918237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1217
      · exact prime_thirtyTwoAD_3220080991709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 47026062802918237) ^ 23513031401459118 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 47026062802918237) ^ 15675354267639412 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 47026062802918237) ^ 38640971900508 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 47026062802918237) ^ 14604 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_55787996463355249 : Nat.Prime 55787996463355249 := by
  apply lucas_primality 55787996463355249 (26 : ZMod 55787996463355249)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (931883, 1), (65642413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (931883, 1), (65642413, 1)] : List FactorBlock).map factorBlockValue).prod) = 55787996463355249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_931883
      · exact prime_thirtyTwoAD_65642413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 55787996463355249) ^ 27893998231677624 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (26 : ZMod 55787996463355249) ^ 18595998821118416 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (26 : ZMod 55787996463355249) ^ 2936210340176592 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (26 : ZMod 55787996463355249) ^ 59865880656 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (26 : ZMod 55787996463355249) ^ 849877296 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_71347522561263737 : Nat.Prime 71347522561263737 := by
  apply lucas_primality 71347522561263737 (3 : ZMod 71347522561263737)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (24581699, 1), (362808133, 1)] : List FactorBlock).map factorBlockValue).prod) = 71347522561263737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_24581699
      · exact prime_thirtyTwoAD_362808133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71347522561263737) ^ 35673761280631868 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 2902465064 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 71347522561263737) ^ 196653592 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_85512338798115589 : Nat.Prime 85512338798115589 := by
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod) = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_t64_71
      · exact prime_thirtyTwoAD_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85512338798115589) ^ 42756169399057794 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 28504112932705196 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1449361674544332 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1204399138001628 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 3569028 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_105440934336291269 : Nat.Prime 105440934336291269 := by
  apply lucas_primality 105440934336291269 (2 : ZMod 105440934336291269)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (184337297790719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (184337297790719, 1)] : List FactorBlock).map factorBlockValue).prod) = 105440934336291269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_184337297790719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105440934336291269) ^ 52720467168145634 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 105440934336291269) ^ 9585539485117388 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 105440934336291269) ^ 8110841102791636 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 105440934336291269) ^ 572 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_121751314820557661 : Nat.Prime 121751314820557661 := by
  apply lucas_primality 121751314820557661 (10 : ZMod 121751314820557661)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (307, 1), (455899, 1), (6213533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (307, 1), (455899, 1), (6213533, 1)] : List FactorBlock).map factorBlockValue).prod) = 121751314820557661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_307
      · exact prime_thirtyTwoAD_455899
      · exact prime_thirtyTwoAD_6213533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 121751314820557661) ^ 60875657410278830 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 121751314820557661) ^ 24350262964111532 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 121751314820557661) ^ 17393044974365380 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 121751314820557661) ^ 396584087363380 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 121751314820557661) ^ 267057648340 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 121751314820557661) ^ 19594539020 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_157125878548354049 : Nat.Prime 157125878548354049 := by
  apply lucas_primality 157125878548354049 (3 : ZMod 157125878548354049)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (67, 1), (127, 1), (18033052153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (67, 1), (127, 1), (18033052153, 1)] : List FactorBlock).map factorBlockValue).prod) = 157125878548354049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_thirtyTwoAD_127
      · exact prime_thirtyTwoAD_18033052153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 157125878548354049) ^ 78562939274177024 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 157125878548354049) ^ 2345162366393344 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 157125878548354049) ^ 1237211642113024 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 157125878548354049) ^ 8713216 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_157899309577893787 : Nat.Prime 157899309577893787 := by
  apply lucas_primality 157899309577893787 (2 : ZMod 157899309577893787)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9042907, 1), (415741019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9042907, 1), (415741019, 1)] : List FactorBlock).map factorBlockValue).prod) = 157899309577893787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_9042907
      · exact prime_thirtyTwoAD_415741019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157899309577893787) ^ 78949654788946893 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 52633103192631262 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 22557044225413398 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 17461122798 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 157899309577893787) ^ 379802094 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_210881868672582539 : Nat.Prime 210881868672582539 := by
  apply lucas_primality 210881868672582539 (2 : ZMod 210881868672582539)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (105440934336291269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (105440934336291269, 1)] : List FactorBlock).map factorBlockValue).prod) = 210881868672582539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_105440934336291269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 210881868672582539) ^ 105440934336291269 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 210881868672582539) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_251500142249756977 : Nat.Prime 251500142249756977 := by
  apply lucas_primality 251500142249756977 (10 : ZMod 251500142249756977)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (111480559507871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (111480559507871, 1)] : List FactorBlock).map factorBlockValue).prod) = 251500142249756977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_thirtyTwoAD_111480559507871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 251500142249756977) ^ 125750071124878488 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 251500142249756977) ^ 83833380749918992 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 251500142249756977) ^ 5351066856377808 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (10 : ZMod 251500142249756977) ^ 2256 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_271912764466122649 : Nat.Prime 271912764466122649 := by
  apply lucas_primality 271912764466122649 (23 : ZMod 271912764466122649)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (93633872061337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (93633872061337, 1)] : List FactorBlock).map factorBlockValue).prod) = 271912764466122649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_93633872061337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 271912764466122649) ^ 135956382233061324 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (23 : ZMod 271912764466122649) ^ 90637588155374216 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (23 : ZMod 271912764466122649) ^ 24719342224192968 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (23 : ZMod 271912764466122649) ^ 2904 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_357575599801727129 : Nat.Prime 357575599801727129 := by
  apply lucas_primality 357575599801727129 (3 : ZMod 357575599801727129)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1567, 1), (10513, 1), (2713202621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1567, 1), (10513, 1), (2713202621, 1)] : List FactorBlock).map factorBlockValue).prod) = 357575599801727129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_1567
      · exact prime_thirtyTwoAD_10513
      · exact prime_thirtyTwoAD_2713202621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 357575599801727129) ^ 178787799900863564 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 357575599801727129) ^ 228191193236584 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 357575599801727129) ^ 34012708056856 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 357575599801727129) ^ 131790968 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_593467097388634319 : Nat.Prime 593467097388634319 := by
  apply lucas_primality 593467097388634319 (7 : ZMod 593467097388634319)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (179, 1), (1740097, 1), (14218879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (179, 1), (1740097, 1), (14218879, 1)] : List FactorBlock).map factorBlockValue).prod) = 593467097388634319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_t64_179
      · exact prime_thirtyTwoAD_1740097
      · exact prime_thirtyTwoAD_14218879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 593467097388634319) ^ 296733548694317159 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 593467097388634319) ^ 8857717871472154 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 593467097388634319) ^ 3315458644629242 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 593467097388634319) ^ 341054031694 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 593467097388634319) ^ 41737966642 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_710602504382600099 : Nat.Prime 710602504382600099 := by
  apply lucas_primality 710602504382600099 (2 : ZMod 710602504382600099)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (73, 1), (167832428999197, 1)] : List FactorBlock).map factorBlockValue).prod) = 710602504382600099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_73
      · exact prime_thirtyTwoAD_167832428999197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 710602504382600099) ^ 355301252191300049 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 24503534633882762 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 9734280881953426 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 710602504382600099) ^ 4234 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_846469130452528267 : Nat.Prime 846469130452528267 := by
  apply lucas_primality 846469130452528267 (2 : ZMod 846469130452528267)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47026062802918237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47026062802918237, 1)] : List FactorBlock).map factorBlockValue).prod) = 846469130452528267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_47026062802918237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 846469130452528267) ^ 423234565226264133 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 846469130452528267) ^ 282156376817509422 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 846469130452528267) ^ 18 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1598901622816847281 : Nat.Prime 1598901622816847281 := by
  apply lucas_primality 1598901622816847281 (41 : ZMod 1598901622816847281)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (29, 1), (47, 1), (9059, 1), (539553341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (29, 1), (47, 1), (9059, 1), (539553341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1598901622816847281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_t64_47
      · exact prime_thirtyTwoAD_9059
      · exact prime_thirtyTwoAD_539553341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 1598901622816847281) ^ 799450811408423640 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 532967207605615760 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 319780324563369456 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 55134538717822320 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 34019183464188240 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 176498688907920 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (41 : ZMod 1598901622816847281) ^ 2963380080 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_4380046674103955719 : Nat.Prime 4380046674103955719 := by
  apply lucas_primality 4380046674103955719 (13 : ZMod 4380046674103955719)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (739, 1), (1823, 1), (180623862983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (739, 1), (1823, 1), (180623862983, 1)] : List FactorBlock).map factorBlockValue).prod) = 4380046674103955719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_739
      · exact prime_thirtyTwoAD_1823
      · exact prime_thirtyTwoAD_180623862983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4380046674103955719) ^ 2190023337051977859 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 4380046674103955719) ^ 1460015558034651906 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 4380046674103955719) ^ 5926991439924162 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 4380046674103955719) ^ 2402658625399866 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (13 : ZMod 4380046674103955719) ^ 24249546 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_4727527780613143369 : Nat.Prime 4727527780613143369 := by
  apply lucas_primality 4727527780613143369 (7 : ZMod 4727527780613143369)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (2459, 1), (11839, 1), (12841, 1), (27733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (2459, 1), (11839, 1), (12841, 1), (27733, 1)] : List FactorBlock).map factorBlockValue).prod) = 4727527780613143369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_2459
      · exact prime_thirtyTwoAD_11839
      · exact prime_thirtyTwoAD_12841
      · exact prime_thirtyTwoAD_27733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4727527780613143369) ^ 2363763890306571684 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 1575842593537714456 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 248817251611218072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 1922540781054552 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 399318167126712 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 368158849047048 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 4727527780613143369) ^ 170465790957096 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_6634509058759861109 : Nat.Prime 6634509058759861109 := by
  apply lucas_primality 6634509058759861109 (2 : ZMod 6634509058759861109)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (97, 1), (289817799176999, 1)] : List FactorBlock).map factorBlockValue).prod) = 6634509058759861109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_97
      · exact prime_thirtyTwoAD_289817799176999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6634509058759861109) ^ 3317254529379930554 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 112449306080675612 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 68397000605771764 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 6634509058759861109) ^ 22892 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_7071559810016419951 : Nat.Prime 7071559810016419951 := by
  apply lucas_primality 7071559810016419951 (3 : ZMod 7071559810016419951)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (9769, 1), (26863, 1), (179646739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (9769, 1), (26863, 1), (179646739, 1)] : List FactorBlock).map factorBlockValue).prod) = 7071559810016419951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_9769
      · exact prime_thirtyTwoAD_26863
      · exact prime_thirtyTwoAD_179646739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7071559810016419951) ^ 3535779905008209975 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7071559810016419951) ^ 2357186603338806650 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7071559810016419951) ^ 1414311962003283990 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7071559810016419951) ^ 723877552463550 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7071559810016419951) ^ 263245348993650 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 7071559810016419951) ^ 39363697050 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_8308539363440880467 : Nat.Prime 8308539363440880467 := by
  apply lucas_primality 8308539363440880467 (2 : ZMod 8308539363440880467)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (593467097388634319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (593467097388634319, 1)] : List FactorBlock).map factorBlockValue).prod) = 8308539363440880467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyTwoAD_593467097388634319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8308539363440880467) ^ 4154269681720440233 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308539363440880467) ^ 1186934194777268638 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308539363440880467) ^ 14 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_13451362101445396397 : Nat.Prime 13451362101445396397 := by
  apply lucas_primality 13451362101445396397 (2 : ZMod 13451362101445396397)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod) = 13451362101445396397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_347
      · exact prime_thirtyTwoAD_9691183070205617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13451362101445396397) ^ 6725681050722698198 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 38764732280822468 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 1388 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_18910111122452573477 : Nat.Prime 18910111122452573477 := by
  apply lucas_primality 18910111122452573477 (2 : ZMod 18910111122452573477)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4727527780613143369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4727527780613143369, 1)] : List FactorBlock).map factorBlockValue).prod) = 18910111122452573477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_4727527780613143369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 18910111122452573477) ^ 9455055561226286738 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 18910111122452573477) ^ 4 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_19695750783871337207 : Nat.Prime 19695750783871337207 := by
  apply lucas_primality 19695750783871337207 (5 : ZMod 19695750783871337207)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (29363, 1), (3320631977381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (29363, 1), (3320631977381, 1)] : List FactorBlock).map factorBlockValue).prod) = 19695750783871337207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_29363
      · exact prime_thirtyTwoAD_3320631977381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19695750783871337207) ^ 9847875391935668603 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 19695750783871337207) ^ 195007433503676606 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 19695750783871337207) ^ 670767659430962 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 19695750783871337207) ^ 5931326 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_28865922088264225807 : Nat.Prime 28865922088264225807 := by
  apply lucas_primality 28865922088264225807 (3 : ZMod 28865922088264225807)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (821, 1), (9124861, 1), (642191821, 1)] : List FactorBlock).map factorBlockValue).prod) = 28865922088264225807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_821
      · exact prime_thirtyTwoAD_9124861
      · exact prime_thirtyTwoAD_642191821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28865922088264225807) ^ 14432961044132112903 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 9621974029421408602 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 35159466611771286 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 3163436910246 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 28865922088264225807) ^ 44949065286 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_53319157597373334101 : Nat.Prime 53319157597373334101 := by
  apply lucas_primality 53319157597373334101 (2 : ZMod 53319157597373334101)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (191, 1), (383, 1), (6317, 1), (7039, 1), (23417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (191, 1), (383, 1), (6317, 1), (7039, 1), (23417, 1)] : List FactorBlock).map factorBlockValue).prod) = 53319157597373334101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_191
      · exact prime_t64_383
      · exact prime_thirtyTwoAD_6317
      · exact prime_thirtyTwoAD_7039
      · exact prime_thirtyTwoAD_23417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53319157597373334101) ^ 26659578798686667050 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 10663831519474666820 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 7617022513910476300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 279157893179965100 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 139214510698102700 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 8440582174667300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 7574819945641900 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 53319157597373334101) ^ 2276942289677300 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_67945843775149768429 : Nat.Prime 67945843775149768429 := by
  apply lucas_primality 67945843775149768429 (2 : ZMod 67945843775149768429)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (3547, 1), (299287, 1), (761203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (3547, 1), (299287, 1), (761203, 1)] : List FactorBlock).map factorBlockValue).prod) = 67945843775149768429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_3547
      · exact prime_thirtyTwoAD_299287
      · exact prime_thirtyTwoAD_761203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67945843775149768429) ^ 33972921887574884214 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 22648614591716589476 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 9706549110735681204 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 6176894888649978948 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 5226603367319212956 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 19155862355553924 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 227025710355444 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 67945843775149768429) ^ 89261135039076 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_132958270776322326311 : Nat.Prime 132958270776322326311 := by
  apply lucas_primality 132958270776322326311 (7 : ZMod 132958270776322326311)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (85991, 1), (154618821477041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (85991, 1), (154618821477041, 1)] : List FactorBlock).map factorBlockValue).prod) = 132958270776322326311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyTwoAD_85991
      · exact prime_thirtyTwoAD_154618821477041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 132958270776322326311) ^ 66479135388161163155 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 132958270776322326311) ^ 26591654155264465262 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 132958270776322326311) ^ 1546188214770410 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 132958270776322326311) ^ 859910 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_894130464072899249663 : Nat.Prime 894130464072899249663 := by
  apply lucas_primality 894130464072899249663 (5 : ZMod 894130464072899249663)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (87998107, 1), (2958879449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (87998107, 1), (2958879449, 1)] : List FactorBlock).map factorBlockValue).prod) = 894130464072899249663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_87998107
      · exact prime_thirtyTwoAD_2958879449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 894130464072899249663) ^ 447065232036449624831 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 894130464072899249663) ^ 52595909651347014686 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 894130464072899249663) ^ 8852776872008903462 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 894130464072899249663) ^ 10160792027866 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 894130464072899249663) ^ 302185499438 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1145462390006519661311 : Nat.Prime 1145462390006519661311 := by
  apply lucas_primality 1145462390006519661311 (7 : ZMod 1145462390006519661311)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (521, 1), (2999, 1), (5639275250353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (521, 1), (2999, 1), (5639275250353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145462390006519661311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_521
      · exact prime_thirtyTwoAD_2999
      · exact prime_thirtyTwoAD_5639275250353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1145462390006519661311) ^ 572731195003259830655 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145462390006519661311) ^ 229092478001303932262 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145462390006519661311) ^ 88112491538963050870 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145462390006519661311) ^ 2198584241855124110 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145462390006519661311) ^ 381948112706408690 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 1145462390006519661311) ^ 203122270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1347120455114909797607 : Nat.Prime 1347120455114909797607 := by
  apply lucas_primality 1347120455114909797607 (5 : ZMod 1347120455114909797607)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (329747923, 1), (38540602237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (329747923, 1), (38540602237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347120455114909797607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_thirtyTwoAD_329747923
      · exact prime_thirtyTwoAD_38540602237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1347120455114909797607) ^ 673560227557454898803 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347120455114909797607) ^ 25417367077639807502 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347120455114909797607) ^ 4085303837122 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347120455114909797607) ^ 34953279838 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1568056709329216147403 : Nat.Prime 1568056709329216147403 := by
  apply lucas_primality 1568056709329216147403 (2 : ZMod 1568056709329216147403)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (4380046674103955719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (4380046674103955719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1568056709329216147403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_179
      · exact prime_thirtyTwoAD_4380046674103955719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1568056709329216147403) ^ 784028354664608073701 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568056709329216147403) ^ 8760093348207911438 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568056709329216147403) ^ 358 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2462308499137944812741 : Nat.Prime 2462308499137944812741 := by
  apply lucas_primality 2462308499137944812741 (2 : ZMod 2462308499137944812741)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (1598901622816847281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (1598901622816847281, 1)] : List FactorBlock).map factorBlockValue).prod) = 2462308499137944812741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_thirtyTwoAD_1598901622816847281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2462308499137944812741) ^ 1231154249568972406370 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2462308499137944812741) ^ 492461699827588962548 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2462308499137944812741) ^ 351758357019706401820 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2462308499137944812741) ^ 223846227194358619340 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 2462308499137944812741) ^ 1540 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_6872774340039117967867 : Nat.Prime 6872774340039117967867 := by
  apply lucas_primality 6872774340039117967867 (3 : ZMod 6872774340039117967867)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1145462390006519661311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1145462390006519661311, 1)] : List FactorBlock).map factorBlockValue).prod) = 6872774340039117967867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_1145462390006519661311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6872774340039117967867) ^ 3436387170019558983933 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 6872774340039117967867) ^ 2290924780013039322622 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 6872774340039117967867) ^ 6 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_10184155909493432847731 : Nat.Prime 10184155909493432847731 := by
  apply lucas_primality 10184155909493432847731 (2 : ZMod 10184155909493432847731)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (263, 1), (11393, 1), (11633, 1), (29217258659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (263, 1), (11393, 1), (11633, 1), (29217258659, 1)] : List FactorBlock).map factorBlockValue).prod) = 10184155909493432847731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_263
      · exact prime_thirtyTwoAD_11393
      · exact prime_thirtyTwoAD_11633
      · exact prime_thirtyTwoAD_29217258659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10184155909493432847731) ^ 5092077954746716423865 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 10184155909493432847731) ^ 2036831181898686569546 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 10184155909493432847731) ^ 38723026271838147710 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 10184155909493432847731) ^ 893895893047786610 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 10184155909493432847731) ^ 875453959382225810 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 10184155909493432847731) ^ 348566442470 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_25808879958420894961817 : Nat.Prime 25808879958420894961817 := by
  apply lucas_primality 25808879958420894961817 (3 : ZMod 25808879958420894961817)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2543, 1), (6180901, 1), (205248987289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2543, 1), (6180901, 1), (205248987289, 1)] : List FactorBlock).map factorBlockValue).prod) = 25808879958420894961817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_2543
      · exact prime_thirtyTwoAD_6180901
      · exact prime_thirtyTwoAD_205248987289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25808879958420894961817) ^ 12904439979210447480908 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 25808879958420894961817) ^ 10148989366268539112 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 25808879958420894961817) ^ 4175585397407416 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 25808879958420894961817) ^ 125744249944 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_29229349063912647400411 : Nat.Prime 29229349063912647400411 := by
  apply lucas_primality 29229349063912647400411 (12 : ZMod 29229349063912647400411)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (307, 1), (2029, 1), (8707, 1), (308134529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (307, 1), (2029, 1), (8707, 1), (308134529, 1)] : List FactorBlock).map factorBlockValue).prod) = 29229349063912647400411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_53
      · exact prime_t64_307
      · exact prime_thirtyTwoAD_2029
      · exact prime_thirtyTwoAD_8707
      · exact prime_thirtyTwoAD_308134529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 29229349063912647400411) ^ 14614674531956323700205 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 9743116354637549133470 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 5845869812782529480082 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 2657213551264786127310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 551497152149295233970 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 95209606071376701630 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 14405790568710028290 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 3356994264834345630 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 29229349063912647400411) ^ 94859051203290 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_58432243368378452043931 : Nat.Prime 58432243368378452043931 := by
  apply lucas_primality 58432243368378452043931 (2 : ZMod 58432243368378452043931)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (18910111122452573477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (18910111122452573477, 1)] : List FactorBlock).map factorBlockValue).prod) = 58432243368378452043931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_103
      · exact prime_thirtyTwoAD_18910111122452573477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58432243368378452043931) ^ 29216121684189226021965 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 58432243368378452043931) ^ 19477414456126150681310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 58432243368378452043931) ^ 11686448673675690408786 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 58432243368378452043931) ^ 567303333673577204310 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 58432243368378452043931) ^ 3090 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_109790012163122297688161 : Nat.Prime 109790012163122297688161 := by
  apply lucas_primality 109790012163122297688161 (3 : ZMod 109790012163122297688161)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (19, 1), (101, 1), (357575599801727129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (19, 1), (101, 1), (357575599801727129, 1)] : List FactorBlock).map factorBlockValue).prod) = 109790012163122297688161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_101
      · exact prime_thirtyTwoAD_357575599801727129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109790012163122297688161) ^ 54895006081561148844080 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 109790012163122297688161) ^ 21958002432624459537632 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 109790012163122297688161) ^ 5778421692795910404640 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 109790012163122297688161) ^ 1087029823397250472160 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 109790012163122297688161) ^ 307040 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_115913844972318925687037 : Nat.Prime 115913844972318925687037 := by
  apply lucas_primality 115913844972318925687037 (2 : ZMod 115913844972318925687037)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (37, 1), (479, 1), (33368908662535517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (37, 1), (479, 1), (33368908662535517, 1)] : List FactorBlock).map factorBlockValue).prod) = 115913844972318925687037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_t64_479
      · exact prime_thirtyTwoAD_33368908662535517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 115913844972318925687037) ^ 57956922486159462843518 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 115913844972318925687037) ^ 16559120710331275098148 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 115913844972318925687037) ^ 3132806620873484478028 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 115913844972318925687037) ^ 241991325620707569284 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 115913844972318925687037) ^ 3473708 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_219580024326244595376323 : Nat.Prime 219580024326244595376323 := by
  apply lucas_primality 219580024326244595376323 (2 : ZMod 219580024326244595376323)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109790012163122297688161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109790012163122297688161, 1)] : List FactorBlock).map factorBlockValue).prod) = 219580024326244595376323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_109790012163122297688161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 219580024326244595376323) ^ 109790012163122297688161 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 219580024326244595376323) ^ 2 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_289875646803692448724369 : Nat.Prime 289875646803692448724369 := by
  apply lucas_primality 289875646803692448724369 (17 : ZMod 289875646803692448724369)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (13, 1), (19, 1), (251, 1), (8855378596144573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (13, 1), (19, 1), (251, 1), (8855378596144573, 1)] : List FactorBlock).map factorBlockValue).prod) = 289875646803692448724369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_251
      · exact prime_thirtyTwoAD_8855378596144573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 289875646803692448724369) ^ 144937823401846224362184 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 96625215601230816241456 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 26352331527608404429488 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 22298126677207111440336 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 15256612989668023617072 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 1154883054994790632368 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (17 : ZMod 289875646803692448724369) ^ 32734416 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_3061
      · exact prime_thirtyTwoAD_61379
      · exact prime_thirtyTwoAD_382747
      · exact prime_thirtyTwoAD_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_938632965099248562505919 : Nat.Prime 938632965099248562505919 := by
  apply lucas_primality 938632965099248562505919 (7 : ZMod 938632965099248562505919)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3011, 1), (15797, 1), (9866893336187777, 1)] : List FactorBlock).map factorBlockValue).prod) = 938632965099248562505919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyTwoAD_3011
      · exact prime_thirtyTwoAD_15797
      · exact prime_thirtyTwoAD_9866893336187777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 938632965099248562505919) ^ 469316482549624281252959 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 311734628063516626538 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 59418431670522793094 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (7 : ZMod 938632965099248562505919) ^ 95129534 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1797526502175621825455579 : Nat.Prime 1797526502175621825455579 := by
  apply lucas_primality 1797526502175621825455579 (2 : ZMod 1797526502175621825455579)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (157, 1), (17669, 1), (18899, 1), (27143, 1), (8651953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (157, 1), (17669, 1), (18899, 1), (27143, 1), (8651953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1797526502175621825455579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_73
      · exact prime_t64_157
      · exact prime_thirtyTwoAD_17669
      · exact prime_thirtyTwoAD_18899
      · exact prime_thirtyTwoAD_27143
      · exact prime_thirtyTwoAD_8651953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1797526502175621825455579) ^ 898763251087810912727789 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 24623650714734545554186 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 11449213389653642200354 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 101733346662268482962 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 95112254731764740222 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 66224312057459449046 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 1797526502175621825455579) ^ 207759624003461626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_2284711654767214962278131 : Nat.Prime 2284711654767214962278131 := by
  apply lucas_primality 2284711654767214962278131 (12 : ZMod 2284711654767214962278131)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (14741, 1), (271912764466122649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (14741, 1), (271912764466122649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2284711654767214962278131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_thirtyTwoAD_14741
      · exact prime_thirtyTwoAD_271912764466122649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 2284711654767214962278131) ^ 1142355827383607481139065 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 2284711654767214962278131) ^ 761570551589071654092710 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 2284711654767214962278131) ^ 456942330953442992455626 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 2284711654767214962278131) ^ 120247981829853419067270 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 2284711654767214962278131) ^ 154990275745689909930 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (12 : ZMod 2284711654767214962278131) ^ 8402370 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3001629664494629685842873 : Nat.Prime 3001629664494629685842873 := by
  apply lucas_primality 3001629664494629685842873 (3 : ZMod 3001629664494629685842873)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod) = 3001629664494629685842873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_thirtyTwoAD_224359867
      · exact prime_thirtyTwoAD_98372345516581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3001629664494629685842873) ^ 1500814832247314842921436 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 176566450852625275637816 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 13378638990255016 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 30512941912 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_3842037198262446690399469 : Nat.Prime 3842037198262446690399469 := by
  apply lucas_primality 3842037198262446690399469 (2 : ZMod 3842037198262446690399469)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (107, 1), (16301, 1), (9661147067553533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (107, 1), (16301, 1), (9661147067553533, 1)] : List FactorBlock).map factorBlockValue).prod) = 3842037198262446690399469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_107
      · exact prime_thirtyTwoAD_16301
      · exact prime_thirtyTwoAD_9661147067553533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3842037198262446690399469) ^ 1921018599131223345199734 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842037198262446690399469) ^ 1280679066087482230133156 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842037198262446690399469) ^ 202212484119076141599972 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842037198262446690399469) ^ 35906889703387352246724 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842037198262446690399469) ^ 235693343860035991068 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842037198262446690399469) ^ 397679196 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_6310682283784872820744549 : Nat.Prime 6310682283784872820744549 := by
  apply lucas_primality 6310682283784872820744549 (6 : ZMod 6310682283784872820744549)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (58432243368378452043931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (58432243368378452043931, 1)] : List FactorBlock).map factorBlockValue).prod) = 6310682283784872820744549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyTwoAD_58432243368378452043931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 6310682283784872820744549) ^ 3155341141892436410372274 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 6310682283784872820744549) ^ 2103560761261624273581516 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (6 : ZMod 6310682283784872820744549) ^ 108 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_7188398307294378217815613 : Nat.Prime 7188398307294378217815613 := by
  apply lucas_primality 7188398307294378217815613 (5 : ZMod 7188398307294378217815613)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 1), (3928157339, 1), (348963959107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 1), (3928157339, 1), (348963959107, 1)] : List FactorBlock).map factorBlockValue).prod) = 7188398307294378217815613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_thirtyTwoAD_3928157339
      · exact prime_thirtyTwoAD_348963959107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7188398307294378217815613) ^ 3594199153647189108907806 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7188398307294378217815613) ^ 2396132769098126072605204 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7188398307294378217815613) ^ 378336753015493590411348 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7188398307294378217815613) ^ 312539056838886009470244 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7188398307294378217815613) ^ 1829967001557108 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (5 : ZMod 7188398307294378217815613) ^ 20599257085716 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_415742201003190247916083201 : Nat.Prime 415742201003190247916083201 := by
  apply lucas_primality 415742201003190247916083201 (137 : ZMod 415742201003190247916083201)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 415742201003190247916083201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (137 : ZMod 415742201003190247916083201) ^ 207871100501595123958041600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 138580733667730082638694400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 83148440200638049583216640 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 59391743000455749702297600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 37794745545744567992371200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 24455423588422955759769600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 21881168473852118311372800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 18075747869703923822438400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 14335937965627249928140800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 13411038742038395094067200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 11236275702788925619353600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 10140053683004640193075200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 9668423279143959253862400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 8845578744748728679065600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 7844192471758306564454400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 7046477983104919456204800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (137 : ZMod 415742201003190247916083201) ^ 6815445918085086031411200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_450387384420122768575756801 : Nat.Prime 450387384420122768575756801 := by
  apply lucas_primality 450387384420122768575756801 (101 : ZMod 450387384420122768575756801)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 450387384420122768575756801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 450387384420122768575756801) ^ 225193692210061384287878400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 150129128140040922858585600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 90077476884024553715151360 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 64341054917160395510822400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 40944307674556615325068800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 34645183416932520659673600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 26493375554124868739750400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 23704599180006461503987200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 19582060192179250807641600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 15530599462762854088819200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 14528625303874928018572800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 12172632011354669420966400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10985058156588360209164800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10474125219072622525017600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 9582710306811122735654400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 8497875177738165444825600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7633684481696996077555200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7383399744592176534028800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_485032567837055289235430401 : Nat.Prime 485032567837055289235430401 := by
  apply lucas_primality 485032567837055289235430401 (67 : ZMod 485032567837055289235430401)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 485032567837055289235430401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 485032567837055289235430401) ^ 242516283918527644617715200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 161677522612351763078476800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 97006513567411057847086080 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 69290366833865041319347200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 44093869803368662657766400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 28531327519826781719731200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 25528029886160804696601600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 21088372514654577792844800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 16725260959898458249497600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 15646211865711460943078400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 13108988319920413222579200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 11830062630172080225254400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 11279827159001285796172800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 10319841868873516792243200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 9151557883718024325196800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 8220890980289072698905600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (67 : ZMod 485032567837055289235430401) ^ 7951353571099267036646400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_652285177436039871730406401 : Nat.Prime 652285177436039871730406401 := by
  apply lucas_primality 652285177436039871730406401 (87 : ZMod 652285177436039871730406401)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 652285177436039871730406401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (87 : ZMod 652285177436039871730406401) ^ 326142588718019935865203200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 217428392478679957243468800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 130457035487207974346081280 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 93183596776577124532915200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 59298652494185442884582400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 50175782879695374748492800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 38369716319767051278259200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 34330798812423151143705600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 28360225105914777031756800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 21041457336646447475174400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 17629329119892969506227200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15909394571610728578790400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 15169422731070694691404800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 13878408030554039824051200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 12307267498793205126988800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 11055680973492201215769600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (87 : ZMod 652285177436039871730406401) ^ 10693199630099014290662400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1080929722608294644581816321 : Nat.Prime 1080929722608294644581816321 := by
  apply lucas_primality 1080929722608294644581816321 (83 : ZMod 1080929722608294644581816321)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080929722608294644581816321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1080929722608294644581816321) ^ 540464861304147322290908160 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 360309907536098214860605440 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 216185944521658928916363264 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 154418531801184949225973760 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 98266338418935876780165120 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 83148440200638049583216640 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 63584101329899684975400960 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 56891038032015507609569280 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 46996944461230201938339840 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 37273438710630849813166080 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 34868700729299827244574720 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 29214316827251206610319360 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 26364139575812064501995520 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 25137900525774294060042240 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 22998504736346694565570560 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 20394900426571597067581440 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 18320842756072790586132480 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (83 : ZMod 1080929722608294644581816321) ^ 17720159387021223681669120 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem prime_thirtyTwoAD_37832540291290312560363571279 : Nat.Prime 37832540291290312560363571279 := by
  apply lucas_primality 37832540291290312560363571279 (3 : ZMod 37832540291290312560363571279)
  · rw [← thirtyTwoADFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (485032567837055289235430401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (485032567837055289235430401, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyTwoAD_485032567837055289235430401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37832540291290312560363571279) ^ 18916270145645156280181785639 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290312560363571279) ^ 12610846763763437520121190426 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290312560363571279) ^ 2910195407022331735412582406 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290312560363571279) ^ 78 ≠ 1
      rw [← thirtyTwoADFastPow_eq_pow]
      decide

private theorem phi_thirtyTwoAD_37832540291290312560363571200 : Nat.totient 37832540291290312560363571200 = 4978283790699540460339200000 := by
  rw [← show ((([(2, 11), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571201 : Nat.totient 37832540291290312560363571201 = 37832540162416453327025990400 := by
  rw [← show ((([(523703249, 1), (672203149, 1), (107468130101, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_523703249, prime_thirtyTwoAD_672203149, prime_thirtyTwoAD_107468130101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571202 : Nat.totient 37832540291290312560363571202 = 18916270144934553749179141204 := by
  rw [← show ((([(2, 1), (26620044299, 1), (710602504382600099, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_thirtyTwoAD_26620044299, prime_thirtyTwoAD_710602504382600099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571203 : Nat.totient 37832540291290312560363571203 = 25061386963844456030041155360 := by
  rw [← show ((([(3, 1), (211, 1), (619, 1), (114067, 1), (846469130452528267, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyTwoAD_211, prime_thirtyTwoAD_619, prime_thirtyTwoAD_114067, prime_thirtyTwoAD_846469130452528267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571204 : Nat.totient 37832540291290312560363571204 = 18795777323961156236076393216 := by
  rw [← show ((([(2, 2), (157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_157, prime_thirtyTwoAD_4315799, prime_thirtyTwoAD_7041049, prime_thirtyTwoAD_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571205 : Nat.totient 37832540291290312560363571205 = 30261018029526413473286863872 := by
  rw [← show ((([(5, 1), (6299, 1), (144577, 1), (8308539363440880467, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_thirtyTwoAD_6299, prime_thirtyTwoAD_144577, prime_thirtyTwoAD_8308539363440880467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571206 : Nat.totient 37832540291290312560363571206 = 12526140360939021221625098240 := by
  rw [← show ((([(2, 1), (3, 1), (149, 1), (180497, 1), (27902741, 1), (8402550447737, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_149, prime_thirtyTwoAD_180497, prime_thirtyTwoAD_27902741, prime_thirtyTwoAD_8402550447737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571207 : Nat.totient 37832540291290312560363571207 = 32422916559897434340215347968 := by
  rw [← show ((([(7, 1), (7369, 1), (61667, 1), (665053, 1), (17883389214479, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_thirtyTwoAD_7369, prime_thirtyTwoAD_61667, prime_thirtyTwoAD_665053, prime_thirtyTwoAD_17883389214479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571208 : Nat.totient 37832540291290312560363571208 = 18867038531782032696231936000 := by
  rw [← show ((([(2, 3), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_thirtyTwoAD_401, prime_thirtyTwoAD_11069, prime_thirtyTwoAD_53269, prime_thirtyTwoAD_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571209 : Nat.totient 37832540291290312560363571209 = 25071919922910020934524534784 := by
  rw [← show ((([(3, 2), (193, 1), (2129, 1), (3433, 1), (44317043, 1), (67242746707, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_193, prime_thirtyTwoAD_2129, prime_thirtyTwoAD_3433, prime_thirtyTwoAD_44317043, prime_thirtyTwoAD_67242746707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571210 : Nat.totient 37832540291290312560363571210 = 14898170181344162306248359936 := by
  rw [← show ((([(2, 1), (5, 1), (67, 1), (1889, 1), (13693, 1), (39926713, 1), (54675980063, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_67, prime_thirtyTwoAD_1889, prime_thirtyTwoAD_13693, prime_thirtyTwoAD_39926713, prime_thirtyTwoAD_54675980063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571211 : Nat.totient 37832540291290312560363571211 = 34393192810659031499296114080 := by
  rw [← show ((([(11, 1), (1342139, 1), (3356083597, 1), (763558914047, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_thirtyTwoAD_1342139, prime_thirtyTwoAD_3356083597, prime_thirtyTwoAD_763558914047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571212 : Nat.totient 37832540291290312560363571212 = 12585775496994684741323506368 := by
  rw [← show ((([(2, 2), (3, 1), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyTwoAD_503, prime_thirtyTwoAD_15040590709, prime_thirtyTwoAD_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571213 : Nat.totient 37832540291290312560363571213 = 34900774566241873363045502448 := by
  rw [← show ((([(13, 1), (1619, 1), (1797526502175621825455579, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_t64_1619, prime_thirtyTwoAD_1797526502175621825455579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571214 : Nat.totient 37832540291290312560363571214 = 16208314041333824177352192024 := by
  rw [← show ((([(2, 1), (7, 1), (2879, 1), (938632965099248562505919, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_thirtyTwoAD_2879, prime_thirtyTwoAD_938632965099248562505919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571215 : Nat.totient 37832540291290312560363571215 = 20130755850121208721354915840 := by
  rw [← show ((([(3, 1), (5, 1), (433, 1), (925339218577, 1), (6294849896641, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_433, prime_thirtyTwoAD_925339218577, prime_thirtyTwoAD_6294849896641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571216 : Nat.totient 37832540291290312560363571216 = 18916180150877748968060860416 := by
  rw [← show ((([(2, 4), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571217 : Nat.totient 37832540291290312560363571217 = 35242045162874227891568409600 := by
  rw [← show ((([(17, 2), (101, 1), (2819, 1), (1699732763, 1), (270502052749, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_101, prime_thirtyTwoAD_2819, prime_thirtyTwoAD_1699732763, prime_thirtyTwoAD_270502052749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571218 : Nat.totient 37832540291290312560363571218 = 12329361044144473180043243520 := by
  rw [← show ((([(2, 1), (3, 2), (83, 1), (97, 1), (13309, 1), (68891, 1), (284731330549429, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_83, prime_t64_97, prime_thirtyTwoAD_13309, prime_thirtyTwoAD_68891, prime_thirtyTwoAD_284731330549429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571219 : Nat.totient 37832540291290312560363571219 = 35711962790638470986107960416 := by
  rw [← show ((([(19, 1), (277, 1), (7188398307294378217815613, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_thirtyTwoAD_277, prime_thirtyTwoAD_7188398307294378217815613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571220 : Nat.totient 37832540291290312560363571220 = 15132836825899783643358817920 := by
  rw [← show ((([(2, 2), (5, 1), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_thirtyTwoAD_85243, prime_thirtyTwoAD_18480383, prime_thirtyTwoAD_23255671, prime_thirtyTwoAD_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571221 : Nat.totient 37832540291290312560363571221 = 21614394220020474094482679296 := by
  rw [← show ((([(3, 1), (7, 1), (5147, 1), (413994480947, 1), (845468611489, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_thirtyTwoAD_5147, prime_thirtyTwoAD_413994480947, prime_thirtyTwoAD_845468611489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571222 : Nat.totient 37832540291290312560363571222 = 17196609223312363224373777920 := by
  rw [← show ((([(2, 1), (11, 1), (13424731660273, 1), (128096483851537, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_thirtyTwoAD_13424731660273, prime_thirtyTwoAD_128096483851537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571223 : Nat.totient 37832540291290312560363571223 = 35942611030944906033149184000 := by
  rw [← show ((([(23, 1), (151, 1), (10321, 1), (18919, 1), (55787996463355249, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_thirtyTwoAD_151, prime_thirtyTwoAD_10321, prime_thirtyTwoAD_18919, prime_thirtyTwoAD_55787996463355249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571224 : Nat.totient 37832540291290312560363571224 = 12610846763763437520121190400 := by
  rw [← show ((([(2, 3), (3, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyTwoAD_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571225 : Nat.totient 37832540291290312560363571225 = 30218564319789612463307352000 := by
  rw [← show ((([(5, 2), (647, 1), (43867, 1), (53319157597373334101, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_647, prime_thirtyTwoAD_43867, prime_thirtyTwoAD_53319157597373334101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571226 : Nat.totient 37832540291290312560363571226 = 17458813237250731638273062976 := by
  rw [← show ((([(2, 1), (13, 1), (14347, 1), (15287, 1), (6634509058759861109, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_thirtyTwoAD_14347, prime_thirtyTwoAD_15287, prime_thirtyTwoAD_6634509058759861109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571227 : Nat.totient 37832540291290312560363571227 = 25213863135114110759243719680 := by
  rw [← show ((([(3, 4), (3221, 1), (316001240129, 1), (458881947263, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyTwoAD_3221, prime_thirtyTwoAD_316001240129, prime_thirtyTwoAD_458881947263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571228 : Nat.totient 37832540291290312560363571228 = 16008706018362235401871405056 := by
  rw [← show ((([(2, 2), (7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_79, prime_thirtyTwoAD_1272241326337, prime_thirtyTwoAD_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571229 : Nat.totient 37832540291290312560363571229 = 36463998010084750797958954800 := by
  rw [← show ((([(29, 1), (571, 1), (2284711654767214962278131, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_thirtyTwoAD_571, prime_thirtyTwoAD_2284711654767214962278131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571230 : Nat.totient 37832540291290312560363571230 = 10088677180083373309633644576 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (43687663, 1), (28865922088264225807, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_thirtyTwoAD_43687663, prime_thirtyTwoAD_28865922088264225807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571231 : Nat.totient 37832540291290312560363571231 = 36612135764861893347205664760 := by
  rw [← show ((([(31, 1), (40548411623, 1), (30097468104848087, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_thirtyTwoAD_40548411623, prime_thirtyTwoAD_30097468104848087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571232 : Nat.totient 37832540291290312560363571232 = 18728877245652730232015619072 := by
  rw [← show ((([(2, 5), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571233 : Nat.totient 37832540291290312560363571233 = 22928608614633514713379322000 := by
  rw [← show ((([(3, 1), (11, 1), (112571, 1), (10184155909493432847731, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_thirtyTwoAD_112571, prime_thirtyTwoAD_10184155909493432847731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571234 : Nat.totient 37832540291290312560363571234 = 17795464654558001598715465728 := by
  rw [← show ((([(2, 1), (17, 1), (2287, 1), (59513, 1), (930659839, 1), (8784511289, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_thirtyTwoAD_2287, prime_thirtyTwoAD_59513, prime_thirtyTwoAD_930659839, prime_thirtyTwoAD_8784511289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571235 : Nat.totient 37832540291290312560363571235 = 25942313342599071469963591680 := by
  rw [← show ((([(5, 1), (7, 1), (1080929722608294644581816321, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_thirtyTwoAD_1080929722608294644581816321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571236 : Nat.totient 37832540291290312560363571236 = 12530507976532553963707627776 := by
  rw [← show ((([(2, 2), (3, 2), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_227, prime_thirtyTwoAD_509, prime_thirtyTwoAD_106363, prime_thirtyTwoAD_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571237 : Nat.totient 37832540291290312560363571237 = 36810034415838772381121792400 := by
  rw [← show ((([(37, 1), (7690391, 1), (132958270776322326311, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_thirtyTwoAD_7690391, prime_thirtyTwoAD_132958270776322326311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571238 : Nat.totient 37832540291290312560363571238 = 17909566826827409976127650336 := by
  rw [← show ((([(2, 1), (19, 1), (1613, 1), (132501777739, 1), (4658282623343, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_thirtyTwoAD_1613, prime_thirtyTwoAD_132501777739, prime_thirtyTwoAD_4658282623343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571239 : Nat.totient 37832540291290312560363571239 = 23248349280291259922555520000 := by
  rw [← show ((([(3, 1), (13, 1), (701, 1), (11366041, 1), (121751314820557661, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_thirtyTwoAD_701, prime_thirtyTwoAD_11366041, prime_thirtyTwoAD_121751314820557661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571240 : Nat.totient 37832540291290312560363571240 = 14976786759142478278239616000 := by
  rw [← show ((([(2, 3), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_107, prime_thirtyTwoAD_1013, prime_thirtyTwoAD_144417341, prime_thirtyTwoAD_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571241 : Nat.totient 37832540291290312560363571241 = 36908763050938553466993825280 := by
  rw [← show ((([(41, 1), (35753, 1), (25808879958420894961817, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_thirtyTwoAD_35753, prime_thirtyTwoAD_25808879958420894961817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571242 : Nat.totient 37832540291290312560363571242 = 10598942061869088945441177600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (71, 2), (353, 1), (389, 1), (17573, 1), (74050722409721, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_71, prime_thirtyTwoAD_353, prime_thirtyTwoAD_389, prime_thirtyTwoAD_17573, prime_thirtyTwoAD_74050722409721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571243 : Nat.totient 37832540291290312560363571243 = 36791348210561189507265305568 := by
  rw [← show ((([(43, 1), (229, 1), (3842037198262446690399469, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_229, prime_thirtyTwoAD_3842037198262446690399469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571244 : Nat.totient 37832540291290312560363571244 = 17196407574338606892000215040 := by
  rw [← show ((([(2, 2), (11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_thirtyTwoAD_85313, prime_thirtyTwoAD_219959393, prime_thirtyTwoAD_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571245 : Nat.totient 37832540291290312560363571245 = 20174572889742164377977241728 := by
  rw [← show ((([(3, 2), (5, 1), (7253, 1), (115913844972318925687037, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_thirtyTwoAD_7253, prime_thirtyTwoAD_115913844972318925687037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571246 : Nat.totient 37832540291290312560363571246 = 18093823616003981996311748224 := by
  rw [← show ((([(2, 1), (23, 1), (11527331273, 1), (71347522561263737, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_thirtyTwoAD_11527331273, prime_thirtyTwoAD_71347522561263737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571247 : Nat.totient 37832540291290312560363571247 = 37019713581865266391590912000 := by
  rw [← show ((([(47, 1), (9391, 1), (13411, 1), (55313, 1), (73141, 1), (1579816097, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_thirtyTwoAD_9391, prime_thirtyTwoAD_13411, prime_thirtyTwoAD_55313, prime_thirtyTwoAD_73141, prime_thirtyTwoAD_1579816097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571248 : Nat.totient 37832540291290312560363571248 = 12572397834087191297154048000 := by
  rw [← show ((([(2, 4), (3, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571249 : Nat.totient 37832540291290312560363571249 = 32427835099189724511218918184 := by
  rw [← show ((([(7, 2), (573143, 1), (1347120455114909797607, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_thirtyTwoAD_573143, prime_thirtyTwoAD_1347120455114909797607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571250 : Nat.totient 37832540291290312560363571250 = 15132730785706553209324272000 := by
  rw [← show ((([(2, 1), (5, 4), (55897, 1), (1036459, 1), (522414067849459, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_thirtyTwoAD_55897, prime_thirtyTwoAD_1036459, prime_thirtyTwoAD_522414067849459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571251 : Nat.totient 37832540291290312560363571251 = 23567256349311874565441488896 := by
  rw [← show ((([(3, 1), (17, 1), (139, 1), (776987, 1), (63198229, 1), (108683062133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_139, prime_thirtyTwoAD_776987, prime_thirtyTwoAD_63198229, prime_thirtyTwoAD_108683062133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571252 : Nat.totient 37832540291290312560363571252 = 17395640938693272227543377920 := by
  rw [← show ((([(2, 2), (13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_307, prime_thirtyTwoAD_2011, prime_thirtyTwoAD_100888969, prime_thirtyTwoAD_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571253 : Nat.totient 37832540291290312560363571253 = 37043835098013585729012992256 := by
  rw [← show ((([(53, 1), (1237, 1), (1579, 1), (1733, 1), (210881868672582539, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_thirtyTwoAD_1237, prime_t64_1579, prime_thirtyTwoAD_1733, prime_thirtyTwoAD_210881868672582539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571254 : Nat.totient 37832540291290312560363571254 = 12610843282295425563125778144 := by
  rw [← show ((([(2, 1), (3, 3), (3972037, 1), (41136839, 1), (4287731098507, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyTwoAD_3972037, prime_thirtyTwoAD_41136839, prime_thirtyTwoAD_4287731098507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571255 : Nat.totient 37832540291290312560363571255 = 27262147465950650585616447360 := by
  rw [← show ((([(5, 1), (11, 1), (109, 1), (6310682283784872820744549, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_t64_109, prime_thirtyTwoAD_6310682283784872820744549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571256 : Nat.totient 37832540291290312560363571256 = 16199029605601766108774387808 := by
  rw [← show ((([(2, 3), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_thirtyTwoAD_1087, prime_thirtyTwoAD_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571257 : Nat.totient 37832540291290312560363571257 = 23894235973333735165034385552 := by
  rw [← show ((([(3, 1), (19, 1), (211883927903, 1), (3132511198980767, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_thirtyTwoAD_211883927903, prime_thirtyTwoAD_3132511198980767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571258 : Nat.totient 37832540291290312560363571258 = 18263984968209116408451379200 := by
  rw [← show ((([(2, 1), (29, 1), (652285177436039871730406401, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_thirtyTwoAD_652285177436039871730406401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571259 : Nat.totient 37832540291290312560363571259 = 37176890866023366030366665760 := by
  rw [← show ((([(59, 1), (3613, 1), (9011, 1), (19695750783871337207, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_thirtyTwoAD_3613, prime_thirtyTwoAD_9011, prime_thirtyTwoAD_19695750783871337207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571260 : Nat.totient 37832540291290312560363571260 = 10088525852502985400151095808 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_thirtyTwoAD_66569, prime_thirtyTwoAD_1596046247, prime_thirtyTwoAD_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571261 : Nat.totient 37832540291290312560363571261 = 36751817306715530056730542080 := by
  rw [← show ((([(61, 1), (89, 1), (883, 1), (50227, 1), (157125878548354049, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_t64_89, prime_t64_883, prime_thirtyTwoAD_50227, prime_thirtyTwoAD_157125878548354049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571262 : Nat.totient 37832540291290312560363571262 = 18281076342659919067790352000 := by
  rw [← show ((([(2, 1), (31, 1), (839, 1), (6197, 1), (82301, 1), (1426018778793047, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_thirtyTwoAD_839, prime_thirtyTwoAD_6197, prime_thirtyTwoAD_82301, prime_thirtyTwoAD_1426018778793047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571263 : Nat.totient 37832540291290312560363571263 = 21201346428321062491169472000 := by
  rw [← show ((([(3, 2), (7, 1), (73, 1), (181, 1), (6427, 1), (7071559810016419951, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_73, prime_thirtyTwoAD_181, prime_thirtyTwoAD_6427, prime_thirtyTwoAD_7071559810016419951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571264 : Nat.totient 37832540291290312560363571264 = 18916270130173191852230595200 := by
  rw [← show ((([(2, 6), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571265 : Nat.totient 37832540291290312560363571265 = 27673785528378316136570880000 := by
  rw [← show ((([(5, 1), (13, 1), (191, 1), (263, 1), (2339, 1), (94321, 1), (1694851, 1), (30987953, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_191, prime_t64_263, prime_thirtyTwoAD_2339, prime_thirtyTwoAD_94321, prime_thirtyTwoAD_1694851, prime_thirtyTwoAD_30987953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571266 : Nat.totient 37832540291290312560363571266 = 11461129667245573256539224000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (3499, 1), (13053027349, 1), (12550654586551, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_thirtyTwoAD_3499, prime_thirtyTwoAD_13053027349, prime_thirtyTwoAD_12550654586551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571267 : Nat.totient 37832540291290312560363571267 = 37832504906777820423928128000 := by
  rw [← show ((([(2339107, 1), (2818667, 1), (6585251, 1), (871363393, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_2339107, prime_thirtyTwoAD_2818667, prime_thirtyTwoAD_6585251, prime_thirtyTwoAD_871363393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571268 : Nat.totient 37832540291290312560363571268 = 17778132830762956802022260736 := by
  rw [← show ((([(2, 2), (17, 1), (709, 1), (58337, 1), (13451362101445396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_thirtyTwoAD_709, prime_thirtyTwoAD_58337, prime_thirtyTwoAD_13451362101445396397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571269 : Nat.totient 37832540291290312560363571269 = 24125029162269626509488580208 := by
  rw [← show ((([(3, 1), (23, 1), (349667, 1), (1568056709329216147403, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_thirtyTwoAD_349667, prime_thirtyTwoAD_1568056709329216147403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571270 : Nat.totient 37832540291290312560363571270 = 12971156671261848722052784128 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (344256547937, 1), (1569947948827553, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_thirtyTwoAD_344256547937, prime_thirtyTwoAD_1569947948827553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571271 : Nat.totient 37832540291290312560363571271 = 37832540291261486148443011992 := by
  rw [← show ((([(1312486028963, 1), (28825099434530317, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_1312486028963, prime_thirtyTwoAD_28825099434530317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571272 : Nat.totient 37832540291290312560363571272 = 12610846763763437520121190400 := by
  rw [← show ((([(2, 3), (3, 2), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyTwoAD_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571273 : Nat.totient 37832540291290312560363571273 = 37600103491607933414526398400 := by
  rw [← show ((([(311, 1), (443, 1), (1861, 1), (6907, 1), (21363163232632363, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_311, prime_thirtyTwoAD_443, prime_thirtyTwoAD_1861, prime_thirtyTwoAD_6907, prime_thirtyTwoAD_21363163232632363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571274 : Nat.totient 37832540291290312560363571274 = 18403967344601959309194152400 := by
  rw [← show ((([(2, 1), (37, 1), (17491, 1), (29229349063912647400411, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_thirtyTwoAD_17491, prime_thirtyTwoAD_29229349063912647400411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571275 : Nat.totient 37832540291290312560363571275 = 20176377275951445737209881600 := by
  rw [← show ((([(3, 1), (5, 2), (20641, 1), (2399393959, 1), (10185255900343, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_thirtyTwoAD_20641, prime_thirtyTwoAD_2399393959, prime_thirtyTwoAD_10185255900343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571276 : Nat.totient 37832540291290312560363571276 = 17920676980038927057667210944 := by
  rw [← show ((([(2, 2), (19, 1), (390056504429, 1), (1276216592026469, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_thirtyTwoAD_390056504429, prime_thirtyTwoAD_1276216592026469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571277 : Nat.totient 37832540291290312560363571277 = 29039902995422716869016987200 := by
  rw [← show ((([(7, 1), (11, 1), (67, 1), (1669603069061, 1), (4392246859823, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_67, prime_thirtyTwoAD_1669603069061, prime_thirtyTwoAD_4392246859823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571278 : Nat.totient 37832540291290312560363571278 = 11640781628089326941650329600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (485032567837055289235430401, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_thirtyTwoAD_485032567837055289235430401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571279 : Nat.totient 37832540291290312560363571279 = 37832540291290312560363571278 := by
  rw [← show ((([(37832540291290312560363571279, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_37832540291290312560363571279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571280 : Nat.totient 37832540291290312560363571280 = 15066202939002796947180304896 := by
  rw [← show ((([(2, 4), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571281 : Nat.totient 37832540291290312560363571281 = 25152735674557747009018736640 := by
  rw [← show ((([(3, 3), (937, 1), (1021, 1), (2137, 1), (4567, 1), (327619, 1), (458069939, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyTwoAD_937, prime_thirtyTwoAD_1021, prime_thirtyTwoAD_2137, prime_thirtyTwoAD_4567, prime_thirtyTwoAD_327619, prime_thirtyTwoAD_458069939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571282 : Nat.totient 37832540291290312560363571282 = 18441876672636518188932249600 := by
  rw [← show ((([(2, 1), (41, 1), (1693, 1), (8699, 1), (232001521, 1), (135031325183, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_thirtyTwoAD_1693, prime_thirtyTwoAD_8699, prime_thirtyTwoAD_232001521, prime_thirtyTwoAD_135031325183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571283 : Nat.totient 37832540291290312560363571283 = 37791038081537342500529473920 := by
  rw [← show ((([(967, 1), (15889, 1), (2462308499137944812741, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_967, prime_thirtyTwoAD_15889, prime_thirtyTwoAD_2462308499137944812741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571284 : Nat.totient 37832540291290312560363571284 = 10809297226082946445818163200 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (450387384420122768575756801, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_thirtyTwoAD_450387384420122768575756801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571285 : Nat.totient 37832540291290312560363571285 = 28471624274238179214875415808 := by
  rw [← show ((([(5, 1), (17, 1), (2027, 1), (219580024326244595376323, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_t64_2027, prime_thirtyTwoAD_219580024326244595376323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571286 : Nat.totient 37832540291290312560363571286 = 18452873579810226421194570240 := by
  rw [← show ((([(2, 1), (43, 1), (881, 1), (7349, 1), (67945843775149768429, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_thirtyTwoAD_881, prime_thirtyTwoAD_7349, prime_thirtyTwoAD_67945843775149768429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571287 : Nat.totient 37832540291290312560363571287 = 24308565308128258846359552000 := by
  rw [← show ((([(3, 1), (29, 1), (761, 1), (2281, 1), (32321, 1), (67074817, 1), (115555873, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_761, prime_t64_2281, prime_thirtyTwoAD_32321, prime_thirtyTwoAD_67074817, prime_thirtyTwoAD_115555873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571288 : Nat.totient 37832540291290312560363571288 = 17193523517369590080698426880 := by
  rw [← show ((([(2, 3), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_thirtyTwoAD_5573, prime_thirtyTwoAD_3198253273, prime_thirtyTwoAD_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571289 : Nat.totient 37832540291290312560363571289 = 37832539397159848487422009524 := by
  rw [← show ((([(42312103, 1), (894130464072899249663, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_42312103, prime_thirtyTwoAD_894130464072899249663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571290 : Nat.totient 37832540291290312560363571290 = 9978683977832279813087846400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (113, 1), (499, 1), (24971, 1), (36341, 1), (8215068638333, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_113, prime_t64_499, prime_thirtyTwoAD_24971, prime_thirtyTwoAD_36341, prime_thirtyTwoAD_8215068638333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571291 : Nat.totient 37832540291290312560363571291 = 29933438472229697849957990400 := by
  rw [← show ((([(7, 1), (13, 1), (415742201003190247916083201, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_thirtyTwoAD_415742201003190247916083201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571292 : Nat.totient 37832540291290312560363571292 = 17961751912335864040083746048 := by
  rw [← show ((([(2, 2), (23, 1), (137, 1), (3001629664494629685842873, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_137, prime_thirtyTwoAD_3001629664494629685842873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571293 : Nat.totient 37832540291290312560363571293 = 24408090042719614389604321920 := by
  rw [← show ((([(3, 1), (31, 2), (52177423, 1), (251500142249756977, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_thirtyTwoAD_52177423, prime_thirtyTwoAD_251500142249756977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571294 : Nat.totient 37832540291290312560363571294 = 18513796305495720767450539032 := by
  rw [← show ((([(2, 1), (47, 1), (2548927123, 1), (157899309577893787, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_thirtyTwoAD_2548927123, prime_thirtyTwoAD_157899309577893787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571295 : Nat.totient 37832540291290312560363571295 = 28305286948566387742505402880 := by
  rw [← show ((([(5, 1), (19, 1), (127, 1), (283, 1), (683, 1), (1254465811, 1), (12932193917, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_thirtyTwoAD_127, prime_t64_283, prime_t64_683, prime_thirtyTwoAD_1254465811, prime_thirtyTwoAD_12932193917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571296 : Nat.totient 37832540291290312560363571296 = 12610846763763437520121190400 := by
  rw [← show ((([(2, 5), (3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571297 : Nat.totient 37832540291290312560363571297 = 37832250415643508867914716416 := by
  rw [← show ((([(130513, 1), (289875646803692448724369, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyTwoAD_130513, prime_thirtyTwoAD_289875646803692448724369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571298 : Nat.totient 37832540291290312560363571298 = 16122835775759527267577832960 := by
  rw [← show ((([(2, 1), (7, 4), (179, 1), (30557, 1), (9420721, 1), (152895766423, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_179, prime_thirtyTwoAD_30557, prime_thirtyTwoAD_9420721, prime_thirtyTwoAD_152895766423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyTwoAD_37832540291290312560363571299 : Nat.totient 37832540291290312560363571299 = 22928399931291302234957119920 := by
  rw [← show ((([(3, 2), (11, 1), (55603, 1), (6872774340039117967867, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290312560363571299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_thirtyTwoAD_55603, prime_thirtyTwoAD_6872774340039117967867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyTwoAD : certifiedKill 1 37832540291290312560363571199 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyTwoAD_37832540291290312560363571200, phi_thirtyTwoAD_37832540291290312560363571201, phi_thirtyTwoAD_37832540291290312560363571202,
    phi_thirtyTwoAD_37832540291290312560363571203, phi_thirtyTwoAD_37832540291290312560363571204, phi_thirtyTwoAD_37832540291290312560363571205,
    phi_thirtyTwoAD_37832540291290312560363571206, phi_thirtyTwoAD_37832540291290312560363571207, phi_thirtyTwoAD_37832540291290312560363571208,
    phi_thirtyTwoAD_37832540291290312560363571209, phi_thirtyTwoAD_37832540291290312560363571210, phi_thirtyTwoAD_37832540291290312560363571211,
    phi_thirtyTwoAD_37832540291290312560363571212, phi_thirtyTwoAD_37832540291290312560363571213, phi_thirtyTwoAD_37832540291290312560363571214,
    phi_thirtyTwoAD_37832540291290312560363571215, phi_thirtyTwoAD_37832540291290312560363571216, phi_thirtyTwoAD_37832540291290312560363571217,
    phi_thirtyTwoAD_37832540291290312560363571218, phi_thirtyTwoAD_37832540291290312560363571219, phi_thirtyTwoAD_37832540291290312560363571220,
    phi_thirtyTwoAD_37832540291290312560363571221, phi_thirtyTwoAD_37832540291290312560363571222, phi_thirtyTwoAD_37832540291290312560363571223,
    phi_thirtyTwoAD_37832540291290312560363571224, phi_thirtyTwoAD_37832540291290312560363571225, phi_thirtyTwoAD_37832540291290312560363571226,
    phi_thirtyTwoAD_37832540291290312560363571227, phi_thirtyTwoAD_37832540291290312560363571228, phi_thirtyTwoAD_37832540291290312560363571229,
    phi_thirtyTwoAD_37832540291290312560363571230, phi_thirtyTwoAD_37832540291290312560363571231, phi_thirtyTwoAD_37832540291290312560363571232,
    phi_thirtyTwoAD_37832540291290312560363571233, phi_thirtyTwoAD_37832540291290312560363571234, phi_thirtyTwoAD_37832540291290312560363571235,
    phi_thirtyTwoAD_37832540291290312560363571236, phi_thirtyTwoAD_37832540291290312560363571237, phi_thirtyTwoAD_37832540291290312560363571238,
    phi_thirtyTwoAD_37832540291290312560363571239, phi_thirtyTwoAD_37832540291290312560363571240, phi_thirtyTwoAD_37832540291290312560363571241,
    phi_thirtyTwoAD_37832540291290312560363571242, phi_thirtyTwoAD_37832540291290312560363571243, phi_thirtyTwoAD_37832540291290312560363571244,
    phi_thirtyTwoAD_37832540291290312560363571245, phi_thirtyTwoAD_37832540291290312560363571246, phi_thirtyTwoAD_37832540291290312560363571247,
    phi_thirtyTwoAD_37832540291290312560363571248, phi_thirtyTwoAD_37832540291290312560363571249, phi_thirtyTwoAD_37832540291290312560363571250,
    phi_thirtyTwoAD_37832540291290312560363571251, phi_thirtyTwoAD_37832540291290312560363571252, phi_thirtyTwoAD_37832540291290312560363571253,
    phi_thirtyTwoAD_37832540291290312560363571254, phi_thirtyTwoAD_37832540291290312560363571255, phi_thirtyTwoAD_37832540291290312560363571256,
    phi_thirtyTwoAD_37832540291290312560363571257, phi_thirtyTwoAD_37832540291290312560363571258, phi_thirtyTwoAD_37832540291290312560363571259,
    phi_thirtyTwoAD_37832540291290312560363571260, phi_thirtyTwoAD_37832540291290312560363571261, phi_thirtyTwoAD_37832540291290312560363571262,
    phi_thirtyTwoAD_37832540291290312560363571263, phi_thirtyTwoAD_37832540291290312560363571264, phi_thirtyTwoAD_37832540291290312560363571265,
    phi_thirtyTwoAD_37832540291290312560363571266, phi_thirtyTwoAD_37832540291290312560363571267, phi_thirtyTwoAD_37832540291290312560363571268,
    phi_thirtyTwoAD_37832540291290312560363571269, phi_thirtyTwoAD_37832540291290312560363571270, phi_thirtyTwoAD_37832540291290312560363571271,
    phi_thirtyTwoAD_37832540291290312560363571272, phi_thirtyTwoAD_37832540291290312560363571273, phi_thirtyTwoAD_37832540291290312560363571274,
    phi_thirtyTwoAD_37832540291290312560363571275, phi_thirtyTwoAD_37832540291290312560363571276, phi_thirtyTwoAD_37832540291290312560363571277,
    phi_thirtyTwoAD_37832540291290312560363571278, phi_thirtyTwoAD_37832540291290312560363571279, phi_thirtyTwoAD_37832540291290312560363571280,
    phi_thirtyTwoAD_37832540291290312560363571281, phi_thirtyTwoAD_37832540291290312560363571282, phi_thirtyTwoAD_37832540291290312560363571283,
    phi_thirtyTwoAD_37832540291290312560363571284, phi_thirtyTwoAD_37832540291290312560363571285, phi_thirtyTwoAD_37832540291290312560363571286,
    phi_thirtyTwoAD_37832540291290312560363571287, phi_thirtyTwoAD_37832540291290312560363571288, phi_thirtyTwoAD_37832540291290312560363571289,
    phi_thirtyTwoAD_37832540291290312560363571290, phi_thirtyTwoAD_37832540291290312560363571291, phi_thirtyTwoAD_37832540291290312560363571292,
    phi_thirtyTwoAD_37832540291290312560363571293, phi_thirtyTwoAD_37832540291290312560363571294, phi_thirtyTwoAD_37832540291290312560363571295,
    phi_thirtyTwoAD_37832540291290312560363571296, phi_thirtyTwoAD_37832540291290312560363571297, phi_thirtyTwoAD_37832540291290312560363571298,
    phi_thirtyTwoAD_37832540291290312560363571299]

end TotientTailPeriodKiller
end Erdos249257
