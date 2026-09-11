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
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_283
  prime_t64_307
  prime_t64_317
  prime_t64_349
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_439
  prime_t64_461
  prime_t64_479
  prime_t64_491
  prime_t64_499
  prime_t64_521
  prime_t64_641
  prime_t64_719
  prime_t64_991
  prime_t64_1061
  prime_t64_1151
  prime_t64_1483
  prime_t64_1619
  prime_t64_2897
  prime_t64_2909
  prime_t64_3739
  prime_t64_4327
  prime_t64_5009
  prime_t64_45127
  prime_t64_97523
  prime_t64_210193
  prime_t64_1214459
  prime_t64_2072201
  prime_t64_2567179
  prime_t64_9492089
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private def fourteenLFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fourteenLFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fourteenLFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fourteenLFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fourteenLFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fourteenLFastPow a n * fourteenLFastPow a n * a
        else fourteenLFastPow a n * fourteenLFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fourteenL_127 : Nat.Prime 127 := by norm_num

private theorem prime_fourteenL_131 : Nat.Prime 131 := by norm_num

private theorem prime_fourteenL_151 : Nat.Prime 151 := by norm_num

private theorem prime_fourteenL_173 : Nat.Prime 173 := by norm_num

private theorem prime_fourteenL_211 : Nat.Prime 211 := by norm_num

private theorem prime_fourteenL_241 : Nat.Prime 241 := by norm_num

private theorem prime_fourteenL_257 : Nat.Prime 257 := by norm_num

private theorem prime_fourteenL_281 : Nat.Prime 281 := by norm_num

private theorem prime_fourteenL_293 : Nat.Prime 293 := by norm_num

private theorem prime_fourteenL_347 : Nat.Prime 347 := by norm_num

private theorem prime_fourteenL_359 : Nat.Prime 359 := by norm_num

private theorem prime_fourteenL_367 : Nat.Prime 367 := by norm_num

private theorem prime_fourteenL_379 : Nat.Prime 379 := by norm_num

private theorem prime_fourteenL_389 : Nat.Prime 389 := by norm_num

private theorem prime_fourteenL_419 : Nat.Prime 419 := by norm_num

private theorem prime_fourteenL_443 : Nat.Prime 443 := by norm_num

private theorem prime_fourteenL_457 : Nat.Prime 457 := by norm_num

private theorem prime_fourteenL_487 : Nat.Prime 487 := by norm_num

private theorem prime_fourteenL_587 : Nat.Prime 587 := by norm_num

private theorem prime_fourteenL_593 : Nat.Prime 593 := by norm_num

private theorem prime_fourteenL_601 : Nat.Prime 601 := by norm_num

private theorem prime_fourteenL_613 : Nat.Prime 613 := by norm_num

private theorem prime_fourteenL_619 : Nat.Prime 619 := by norm_num

private theorem prime_fourteenL_643 : Nat.Prime 643 := by norm_num

private theorem prime_fourteenL_677 : Nat.Prime 677 := by norm_num

private theorem prime_fourteenL_709 : Nat.Prime 709 := by norm_num

private theorem prime_fourteenL_757 : Nat.Prime 757 := by norm_num

private theorem prime_fourteenL_853 : Nat.Prime 853 := by norm_num

private theorem prime_fourteenL_937 : Nat.Prime 937 := by norm_num

private theorem prime_fourteenL_953 : Nat.Prime 953 := by norm_num

private theorem prime_fourteenL_967 : Nat.Prime 967 := by norm_num

private theorem prime_fourteenL_971 : Nat.Prime 971 := by norm_num

private theorem prime_fourteenL_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_fourteenL_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_fourteenL_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_fourteenL_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_fourteenL_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_fourteenL_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_fourteenL_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_fourteenL_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_fourteenL_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_fourteenL_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_fourteenL_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_fourteenL_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_fourteenL_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_fourteenL_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_fourteenL_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_fourteenL_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_fourteenL_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_fourteenL_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_fourteenL_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_fourteenL_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_fourteenL_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_fourteenL_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_fourteenL_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_fourteenL_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_fourteenL_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_fourteenL_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_fourteenL_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_fourteenL_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_fourteenL_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_fourteenL_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_fourteenL_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_fourteenL_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_fourteenL_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_fourteenL_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_fourteenL_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_fourteenL_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_fourteenL_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_fourteenL_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_fourteenL_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_fourteenL_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_fourteenL_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_fourteenL_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_fourteenL_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_fourteenL_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_fourteenL_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_fourteenL_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_fourteenL_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_fourteenL_3301 : Nat.Prime 3301 := by norm_num

private theorem prime_fourteenL_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_fourteenL_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_fourteenL_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_fourteenL_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_fourteenL_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_fourteenL_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_fourteenL_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_fourteenL_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_fourteenL_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_fourteenL_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_fourteenL_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_fourteenL_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_fourteenL_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_fourteenL_4703 : Nat.Prime 4703 := by norm_num

private theorem prime_fourteenL_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_fourteenL_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_fourteenL_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_fourteenL_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_fourteenL_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_fourteenL_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_fourteenL_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_fourteenL_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_fourteenL_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_fourteenL_6271 : Nat.Prime 6271 := by norm_num

private theorem prime_fourteenL_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_fourteenL_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_fourteenL_7211 : Nat.Prime 7211 := by norm_num

private theorem prime_fourteenL_7309 : Nat.Prime 7309 := by norm_num

private theorem prime_fourteenL_7541 : Nat.Prime 7541 := by norm_num

private theorem prime_fourteenL_7681 : Nat.Prime 7681 := by norm_num

private theorem prime_fourteenL_7691 : Nat.Prime 7691 := by norm_num

private theorem prime_fourteenL_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_fourteenL_8219 : Nat.Prime 8219 := by norm_num

private theorem prime_fourteenL_8287 : Nat.Prime 8287 := by norm_num

private theorem prime_fourteenL_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_fourteenL_9161 : Nat.Prime 9161 := by norm_num

private theorem prime_fourteenL_10009 : Nat.Prime 10009 := by norm_num

private theorem prime_fourteenL_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_fourteenL_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_fourteenL_10391 : Nat.Prime 10391 := by norm_num

private theorem prime_fourteenL_10729 : Nat.Prime 10729 := by norm_num

private theorem prime_fourteenL_11399 : Nat.Prime 11399 := by norm_num

private theorem prime_fourteenL_12479 : Nat.Prime 12479 := by norm_num

private theorem prime_fourteenL_12589 : Nat.Prime 12589 := by norm_num

private theorem prime_fourteenL_12689 : Nat.Prime 12689 := by norm_num

private theorem prime_fourteenL_12973 : Nat.Prime 12973 := by norm_num

private theorem prime_fourteenL_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_fourteenL_13229 : Nat.Prime 13229 := by norm_num

private theorem prime_fourteenL_13331 : Nat.Prime 13331 := by norm_num

private theorem prime_fourteenL_13789 : Nat.Prime 13789 := by norm_num

private theorem prime_fourteenL_14449 : Nat.Prime 14449 := by norm_num

private theorem prime_fourteenL_15073 : Nat.Prime 15073 := by norm_num

private theorem prime_fourteenL_15661 : Nat.Prime 15661 := by norm_num

private theorem prime_fourteenL_15683 : Nat.Prime 15683 := by norm_num

private theorem prime_fourteenL_16333 : Nat.Prime 16333 := by norm_num

private theorem prime_fourteenL_16631 : Nat.Prime 16631 := by norm_num

private theorem prime_fourteenL_16943 : Nat.Prime 16943 := by norm_num

private theorem prime_fourteenL_17077 : Nat.Prime 17077 := by norm_num

private theorem prime_fourteenL_18043 : Nat.Prime 18043 := by norm_num

private theorem prime_fourteenL_19379 : Nat.Prime 19379 := by norm_num

private theorem prime_fourteenL_19801 : Nat.Prime 19801 := by norm_num

private theorem prime_fourteenL_20347 : Nat.Prime 20347 := by norm_num

private theorem prime_fourteenL_20549 : Nat.Prime 20549 := by norm_num

private theorem prime_fourteenL_20809 : Nat.Prime 20809 := by norm_num

private theorem prime_fourteenL_22279 : Nat.Prime 22279 := by norm_num

private theorem prime_fourteenL_22543 : Nat.Prime 22543 := by norm_num

private theorem prime_fourteenL_22639 : Nat.Prime 22639 := by norm_num

private theorem prime_fourteenL_22811 : Nat.Prime 22811 := by norm_num

private theorem prime_fourteenL_23339 : Nat.Prime 23339 := by norm_num

private theorem prime_fourteenL_23669 : Nat.Prime 23669 := by norm_num

private theorem prime_fourteenL_24977 : Nat.Prime 24977 := by norm_num

private theorem prime_fourteenL_25457 : Nat.Prime 25457 := by norm_num

private theorem prime_fourteenL_26641 : Nat.Prime 26641 := by norm_num

private theorem prime_fourteenL_28979 : Nat.Prime 28979 := by norm_num

private theorem prime_fourteenL_33811 : Nat.Prime 33811 := by norm_num

private theorem prime_fourteenL_34591 : Nat.Prime 34591 := by norm_num

private theorem prime_fourteenL_34897 : Nat.Prime 34897 := by norm_num

private theorem prime_fourteenL_35461 : Nat.Prime 35461 := by norm_num

private theorem prime_fourteenL_35747 : Nat.Prime 35747 := by norm_num

private theorem prime_fourteenL_35923 : Nat.Prime 35923 := by norm_num

private theorem prime_fourteenL_39227 : Nat.Prime 39227 := by norm_num

private theorem prime_fourteenL_40433 : Nat.Prime 40433 := by norm_num

private theorem prime_fourteenL_42463 : Nat.Prime 42463 := by norm_num

private theorem prime_fourteenL_43331 : Nat.Prime 43331 := by norm_num

private theorem prime_fourteenL_43591 : Nat.Prime 43591 := by norm_num

private theorem prime_fourteenL_45949 : Nat.Prime 45949 := by norm_num

private theorem prime_fourteenL_47791 : Nat.Prime 47791 := by norm_num

private theorem prime_fourteenL_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_fourteenL_49787 : Nat.Prime 49787 := by norm_num

private theorem prime_fourteenL_55711 : Nat.Prime 55711 := by norm_num

private theorem prime_fourteenL_60397 : Nat.Prime 60397 := by norm_num

private theorem prime_fourteenL_61511 : Nat.Prime 61511 := by norm_num

private theorem prime_fourteenL_66239 : Nat.Prime 66239 := by norm_num

private theorem prime_fourteenL_72859 : Nat.Prime 72859 := by norm_num

private theorem prime_fourteenL_72973 : Nat.Prime 72973 := by norm_num

private theorem prime_fourteenL_73819 : Nat.Prime 73819 := by norm_num

private theorem prime_fourteenL_78233 : Nat.Prime 78233 := by norm_num

private theorem prime_fourteenL_82183 : Nat.Prime 82183 := by norm_num

private theorem prime_fourteenL_83609 : Nat.Prime 83609 := by norm_num

private theorem prime_fourteenL_85303 : Nat.Prime 85303 := by norm_num

private theorem prime_fourteenL_90617 : Nat.Prime 90617 := by norm_num

private theorem prime_fourteenL_93179 : Nat.Prime 93179 := by norm_num

private theorem prime_fourteenL_93199 : Nat.Prime 93199 := by norm_num

private theorem prime_fourteenL_95287 : Nat.Prime 95287 := by norm_num

private theorem prime_fourteenL_109621 : Nat.Prime 109621 := by norm_num

private theorem prime_fourteenL_111869 : Nat.Prime 111869 := by norm_num

private theorem prime_fourteenL_112573 : Nat.Prime 112573 := by norm_num

private theorem prime_fourteenL_116443 : Nat.Prime 116443 := by norm_num

private theorem prime_fourteenL_123979 : Nat.Prime 123979 := by norm_num

private theorem prime_fourteenL_127241 : Nat.Prime 127241 := by norm_num

private theorem prime_fourteenL_127487 : Nat.Prime 127487 := by norm_num

private theorem prime_fourteenL_128749 : Nat.Prime 128749 := by norm_num

private theorem prime_fourteenL_130439 : Nat.Prime 130439 := by norm_num

private theorem prime_fourteenL_148537 : Nat.Prime 148537 := by norm_num

private theorem prime_fourteenL_151939 : Nat.Prime 151939 := by norm_num

private theorem prime_fourteenL_152639 : Nat.Prime 152639 := by norm_num

private theorem prime_fourteenL_185531 : Nat.Prime 185531 := by norm_num

private theorem prime_fourteenL_189853 : Nat.Prime 189853 := by norm_num

private theorem prime_fourteenL_190793 : Nat.Prime 190793 := by norm_num

private theorem prime_fourteenL_192931 : Nat.Prime 192931 := by norm_num

private theorem prime_fourteenL_195271 : Nat.Prime 195271 := by norm_num

private theorem prime_fourteenL_201823 : Nat.Prime 201823 := by norm_num

private theorem prime_fourteenL_215497 : Nat.Prime 215497 := by norm_num

private theorem prime_fourteenL_218857 : Nat.Prime 218857 := by norm_num

private theorem prime_fourteenL_222163 : Nat.Prime 222163 := by norm_num

private theorem prime_fourteenL_224897 : Nat.Prime 224897 := by norm_num

private theorem prime_fourteenL_230291 : Nat.Prime 230291 := by norm_num

private theorem prime_fourteenL_239069 : Nat.Prime 239069 := by norm_num

private theorem prime_fourteenL_242633 : Nat.Prime 242633 := by norm_num

private theorem prime_fourteenL_273187 : Nat.Prime 273187 := by norm_num

private theorem prime_fourteenL_275491 : Nat.Prime 275491 := by norm_num

private theorem prime_fourteenL_292483 : Nat.Prime 292483 := by norm_num

private theorem prime_fourteenL_293147 : Nat.Prime 293147 := by norm_num

private theorem prime_fourteenL_302287 : Nat.Prime 302287 := by norm_num

private theorem prime_fourteenL_307817 : Nat.Prime 307817 := by norm_num

private theorem prime_fourteenL_311677 : Nat.Prime 311677 := by norm_num

private theorem prime_fourteenL_316097 : Nat.Prime 316097 := by norm_num

private theorem prime_fourteenL_319919 : Nat.Prime 319919 := by norm_num

private theorem prime_fourteenL_325319 : Nat.Prime 325319 := by norm_num

private theorem prime_fourteenL_343559 : Nat.Prime 343559 := by norm_num

private theorem prime_fourteenL_344543 : Nat.Prime 344543 := by norm_num

private theorem prime_fourteenL_360037 : Nat.Prime 360037 := by norm_num

private theorem prime_fourteenL_363611 : Nat.Prime 363611 := by norm_num

private theorem prime_fourteenL_367219 : Nat.Prime 367219 := by norm_num

private theorem prime_fourteenL_370537 : Nat.Prime 370537 := by norm_num

private theorem prime_fourteenL_394811 : Nat.Prime 394811 := by norm_num

private theorem prime_fourteenL_411449 : Nat.Prime 411449 := by norm_num

private theorem prime_fourteenL_413869 : Nat.Prime 413869 := by norm_num

private theorem prime_fourteenL_425681 : Nat.Prime 425681 := by norm_num

private theorem prime_fourteenL_431891 : Nat.Prime 431891 := by norm_num

private theorem prime_fourteenL_452533 : Nat.Prime 452533 := by norm_num

private theorem prime_fourteenL_512903 : Nat.Prime 512903 := by norm_num

private theorem prime_fourteenL_548897 : Nat.Prime 548897 := by norm_num

private theorem prime_fourteenL_565997 : Nat.Prime 565997 := by norm_num

private theorem prime_fourteenL_576509 : Nat.Prime 576509 := by norm_num

private theorem prime_fourteenL_596093 : Nat.Prime 596093 := by norm_num

private theorem prime_fourteenL_620159 : Nat.Prime 620159 := by norm_num

private theorem prime_fourteenL_635203 : Nat.Prime 635203 := by norm_num

private theorem prime_fourteenL_679153 : Nat.Prime 679153 := by norm_num

private theorem prime_fourteenL_692663 : Nat.Prime 692663 := by norm_num

private theorem prime_fourteenL_758159 : Nat.Prime 758159 := by norm_num

private theorem prime_fourteenL_812249 : Nat.Prime 812249 := by norm_num

private theorem prime_fourteenL_865957 : Nat.Prime 865957 := by norm_num

private theorem prime_fourteenL_888691 : Nat.Prime 888691 := by norm_num

private theorem prime_fourteenL_914737 : Nat.Prime 914737 := by norm_num

private theorem prime_fourteenL_951637 : Nat.Prime 951637 := by norm_num

private theorem prime_fourteenL_1014907 : Nat.Prime 1014907 := by norm_num

private theorem prime_fourteenL_1088443 : Nat.Prime 1088443 := by norm_num

private theorem prime_fourteenL_1099177 : Nat.Prime 1099177 := by norm_num

private theorem prime_fourteenL_1173959 : Nat.Prime 1173959 := by norm_num

private theorem prime_fourteenL_1179173 : Nat.Prime 1179173 := by norm_num

private theorem prime_fourteenL_1305709 : Nat.Prime 1305709 := by norm_num

private theorem prime_fourteenL_1346333 : Nat.Prime 1346333 := by norm_num

private theorem prime_fourteenL_1489003 : Nat.Prime 1489003 := by norm_num

private theorem prime_fourteenL_1512041 : Nat.Prime 1512041 := by norm_num

private theorem prime_fourteenL_1588921 : Nat.Prime 1588921 := by norm_num

private theorem prime_fourteenL_1693169 : Nat.Prime 1693169 := by norm_num

private theorem prime_fourteenL_1694081 : Nat.Prime 1694081 := by norm_num

private theorem prime_fourteenL_1881863 : Nat.Prime 1881863 := by norm_num

private theorem prime_fourteenL_1957301 : Nat.Prime 1957301 := by norm_num

private theorem prime_fourteenL_2290081 : Nat.Prime 2290081 := by norm_num

private theorem prime_fourteenL_2376989 : Nat.Prime 2376989 := by norm_num

private theorem prime_fourteenL_2536943 : Nat.Prime 2536943 := by norm_num

private theorem prime_fourteenL_2633923 : Nat.Prime 2633923 := by norm_num

private theorem prime_fourteenL_2643737 : Nat.Prime 2643737 := by norm_num

private theorem prime_fourteenL_2740211 : Nat.Prime 2740211 := by norm_num

private theorem prime_fourteenL_2846287 : Nat.Prime 2846287 := by norm_num

private theorem prime_fourteenL_2909383 : Nat.Prime 2909383 := by norm_num

private theorem prime_fourteenL_2993957 : Nat.Prime 2993957 := by norm_num

private theorem prime_fourteenL_3015373 : Nat.Prime 3015373 := by norm_num

private theorem prime_fourteenL_3369409 : Nat.Prime 3369409 := by norm_num

private theorem prime_fourteenL_3532679 : Nat.Prime 3532679 := by norm_num

private theorem prime_fourteenL_3600853 : Nat.Prime 3600853 := by norm_num

private theorem prime_fourteenL_3779417 : Nat.Prime 3779417 := by norm_num

private theorem prime_fourteenL_3818077 : Nat.Prime 3818077 := by norm_num

private theorem prime_fourteenL_5024819 : Nat.Prime 5024819 := by norm_num

private theorem prime_fourteenL_5572883 : Nat.Prime 5572883 := by norm_num

private theorem prime_fourteenL_5944361 : Nat.Prime 5944361 := by norm_num

private theorem prime_fourteenL_6135331 : Nat.Prime 6135331 := by norm_num

private theorem prime_fourteenL_6303503 : Nat.Prime 6303503 := by norm_num

private theorem prime_fourteenL_6470753 : Nat.Prime 6470753 := by norm_num

private theorem prime_fourteenL_6475879 : Nat.Prime 6475879 := by norm_num

private theorem prime_fourteenL_6939487 : Nat.Prime 6939487 := by norm_num

private theorem prime_fourteenL_7658927 : Nat.Prime 7658927 := by norm_num

private theorem prime_fourteenL_7780667 : Nat.Prime 7780667 := by norm_num

private theorem prime_fourteenL_7833299 : Nat.Prime 7833299 := by norm_num

private theorem prime_fourteenL_7978459 : Nat.Prime 7978459 := by norm_num

private theorem prime_fourteenL_10049639 : Nat.Prime 10049639 := by
  apply lucas_primality 10049639 (13 : ZMod 10049639)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5024819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5024819, 1)] : List FactorBlock).map factorBlockValue).prod) = 10049639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_5024819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 10049639) ^ 5024819 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 10049639) ^ 2 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_10167809 : Nat.Prime 10167809 := by
  apply lucas_primality 10167809 (6 : ZMod 10167809)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (7, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (7, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod) = 10167809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_fourteenL_2837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 10167809) ^ 5083904 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 10167809) ^ 1452544 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 10167809) ^ 3584 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_12226771 : Nat.Prime 12226771 := by
  apply lucas_primality 12226771 (3 : ZMod 12226771)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (73, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (73, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 12226771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_73
      · exact prime_fourteenL_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12226771) ^ 6113385 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12226771) ^ 4075590 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12226771) ^ 2445354 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12226771) ^ 167490 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12226771) ^ 6570 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_13061317 : Nat.Prime 13061317 := by
  apply lucas_primality 13061317 (2 : ZMod 13061317)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1088443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1088443, 1)] : List FactorBlock).map factorBlockValue).prod) = 13061317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_1088443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13061317) ^ 6530658 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13061317) ^ 4353772 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13061317) ^ 12 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_13166369 : Nat.Prime 13166369 := by
  apply lucas_primality 13166369 (3 : ZMod 13166369)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (411449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (411449, 1)] : List FactorBlock).map factorBlockValue).prod) = 13166369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_411449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13166369) ^ 6583184 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13166369) ^ 32 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_13505171 : Nat.Prime 13505171 := by
  apply lucas_primality 13505171 (7 : ZMod 13505171)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (192931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (192931, 1)] : List FactorBlock).map factorBlockValue).prod) = 13505171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_fourteenL_192931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13505171) ^ 6752585 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 13505171) ^ 2701034 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 13505171) ^ 1929310 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 13505171) ^ 70 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_15959533 : Nat.Prime 15959533 := by
  apply lucas_primality 15959533 (2 : ZMod 15959533)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (78233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (78233, 1)] : List FactorBlock).map factorBlockValue).prod) = 15959533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_fourteenL_78233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15959533) ^ 7979766 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15959533) ^ 5319844 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15959533) ^ 938796 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15959533) ^ 204 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_16477079 : Nat.Prime 16477079 := by
  apply lucas_primality 16477079 (11 : ZMod 16477079)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2243, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2243, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 16477079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_2243
      · exact prime_fourteenL_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 16477079) ^ 8238539 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 16477079) ^ 7346 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 16477079) ^ 4486 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_17290739 : Nat.Prime 17290739 := by
  apply lucas_primality 17290739 (2 : ZMod 17290739)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (22811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (22811, 1)] : List FactorBlock).map factorBlockValue).prod) = 17290739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_379
      · exact prime_fourteenL_22811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17290739) ^ 8645369 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17290739) ^ 45622 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17290739) ^ 758 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_18142381 : Nat.Prime 18142381 := by
  apply lucas_primality 18142381 (6 : ZMod 18142381)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) = 18142381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_3733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 18142381) ^ 9071190 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 18142381) ^ 6047460 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 18142381) ^ 3628476 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 18142381) ^ 4860 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_18223631 : Nat.Prime 18223631 := by
  apply lucas_primality 18223631 (19 : ZMod 18223631)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (641, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (641, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) = 18223631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_641
      · exact prime_fourteenL_2843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 18223631) ^ 9111815 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (19 : ZMod 18223631) ^ 3644726 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (19 : ZMod 18223631) ^ 28430 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (19 : ZMod 18223631) ^ 6410 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_20354891 : Nat.Prime 20354891 := by
  apply lucas_primality 20354891 (2 : ZMod 20354891)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 20354891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_149
      · exact prime_t64_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20354891) ^ 10177445 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 4070978 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 1071310 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 136610 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 28310 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_20980153 : Nat.Prime 20980153 := by
  apply lucas_primality 20980153 (5 : ZMod 20980153)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (211, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (211, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) = 20980153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_211
      · exact prime_fourteenL_1381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20980153) ^ 10490076 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20980153) ^ 6993384 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20980153) ^ 99432 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20980153) ^ 15192 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_22951043 : Nat.Prime 22951043 := by
  apply lucas_primality 22951043 (2 : ZMod 22951043)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) = 22951043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1303
      · exact prime_fourteenL_8807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22951043) ^ 11475521 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 17614 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 2606 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_23153183 : Nat.Prime 23153183 := by
  apply lucas_primality 23153183 (5 : ZMod 23153183)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (83, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (83, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) = 23153183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_83
      · exact prime_fourteenL_10729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23153183) ^ 11576591 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 1781014 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 278954 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 2158 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_24993457 : Nat.Prime 24993457 := by
  apply lucas_primality 24993457 (5 : ZMod 24993457)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (22639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (22639, 1)] : List FactorBlock).map factorBlockValue).prod) = 24993457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_fourteenL_22639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24993457) ^ 12496728 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 8331152 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 1086672 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 1104 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_27075547 : Nat.Prime 27075547 := by
  apply lucas_primality 27075547 (3 : ZMod 27075547)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (55711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (55711, 1)] : List FactorBlock).map factorBlockValue).prod) = 27075547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_55711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27075547) ^ 13537773 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 27075547) ^ 9025182 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 27075547) ^ 486 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_27757949 : Nat.Prime 27757949 := by
  apply lucas_primality 27757949 (2 : ZMod 27757949)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6939487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6939487, 1)] : List FactorBlock).map factorBlockValue).prod) = 27757949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_6939487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 27757949) ^ 13878974 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 27757949) ^ 4 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_29059717 : Nat.Prime 29059717 := by
  apply lucas_primality 29059717 (5 : ZMod 29059717)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (457, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (457, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 29059717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_fourteenL_457
      · exact prime_fourteenL_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29059717) ^ 14529858 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29059717) ^ 9686572 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29059717) ^ 4151388 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29059717) ^ 63588 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29059717) ^ 38388 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_36575219 : Nat.Prime 36575219 := by
  apply lucas_primality 36575219 (2 : ZMod 36575219)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (251, 1), (72859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (251, 1), (72859, 1)] : List FactorBlock).map factorBlockValue).prod) = 36575219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_251
      · exact prime_fourteenL_72859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36575219) ^ 18287609 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36575219) ^ 145718 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36575219) ^ 502 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_43585393 : Nat.Prime 43585393 := by
  apply lucas_primality 43585393 (7 : ZMod 43585393)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (47791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (47791, 1)] : List FactorBlock).map factorBlockValue).prod) = 43585393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_fourteenL_47791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 43585393) ^ 21792696 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 43585393) ^ 14528464 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 43585393) ^ 2293968 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 43585393) ^ 912 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_fourteenL_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_56438293 : Nat.Prime 56438293 := by
  apply lucas_primality 56438293 (2 : ZMod 56438293)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (127, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (127, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) = 56438293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_fourteenL_127
      · exact prime_fourteenL_1277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56438293) ^ 28219146 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 18812764 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 1946148 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 444396 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 44196 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_73271521 : Nat.Prime 73271521 := by
  apply lucas_primality 73271521 (13 : ZMod 73271521)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 73271521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_fourteenL_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 73271521) ^ 36635760 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 24423840 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 14654304 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 10467360 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 30240 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_75997183 : Nat.Prime 75997183 := by
  apply lucas_primality 75997183 (3 : ZMod 75997183)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 75997183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_479
      · exact prime_fourteenL_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75997183) ^ 37998591 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 25332394 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 2451522 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 158658 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 89094 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_90735599 : Nat.Prime 90735599 := by
  apply lucas_primality 90735599 (11 : ZMod 90735599)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) = 90735599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_fourteenL_151
      · exact prime_fourteenL_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90735599) ^ 45367799 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 3945026 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 600898 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 6946 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_116512763 : Nat.Prime 116512763 := by
  apply lucas_primality 116512763 (2 : ZMod 116512763)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod) = 116512763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_fourteenL_1099177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116512763) ^ 58256381 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 2198354 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 106 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_116899877 : Nat.Prime 116899877 := by
  apply lucas_primality 116899877 (2 : ZMod 116899877)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (587, 1), (49787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (587, 1), (49787, 1)] : List FactorBlock).map factorBlockValue).prod) = 116899877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_587
      · exact prime_fourteenL_49787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116899877) ^ 58449938 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116899877) ^ 199148 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116899877) ^ 2348 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_122267711 : Nat.Prime 122267711 := by
  apply lucas_primality 122267711 (11 : ZMod 122267711)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12226771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12226771, 1)] : List FactorBlock).map factorBlockValue).prod) = 122267711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_12226771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 122267711) ^ 61133855 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 122267711) ^ 24453542 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 122267711) ^ 10 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_137616691 : Nat.Prime 137616691 := by
  apply lucas_primality 137616691 (2 : ZMod 137616691)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (123979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (123979, 1)] : List FactorBlock).map factorBlockValue).prod) = 137616691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_fourteenL_123979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137616691) ^ 68808345 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 137616691) ^ 45872230 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 137616691) ^ 27523338 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 137616691) ^ 3719370 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 137616691) ^ 1110 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_143078893 : Nat.Prime 143078893 := by
  apply lucas_primality 143078893 (5 : ZMod 143078893)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 143078893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_t64_89
      · exact prime_t64_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 143078893) ^ 71539446 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 47692964 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 13007172 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 7530468 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 1607628 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 223212 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_156665981 : Nat.Prime 156665981 := by
  apply lucas_primality 156665981 (2 : ZMod 156665981)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7833299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7833299, 1)] : List FactorBlock).map factorBlockValue).prod) = 156665981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_7833299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 156665981) ^ 78332990 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 156665981) ^ 31333196 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 156665981) ^ 20 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_169985287 : Nat.Prime 169985287 := by
  apply lucas_primality 169985287 (3 : ZMod 169985287)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 169985287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_307
      · exact prime_t64_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 169985287) ^ 84992643 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 56661762 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 8946594 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 553698 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 104994 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_197209589 : Nat.Prime 197209589 := by
  apply lucas_primality 197209589 (2 : ZMod 197209589)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (152639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (152639, 1)] : List FactorBlock).map factorBlockValue).prod) = 197209589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_fourteenL_152639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197209589) ^ 98604794 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 11600564 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 10379452 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 1292 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_209801531 : Nat.Prime 209801531 := by
  apply lucas_primality 209801531 (6 : ZMod 209801531)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) = 209801531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_20980153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 209801531) ^ 104900765 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 41960306 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 10 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_fourteenL_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_229713433 : Nat.Prime 229713433 := by
  apply lucas_primality 229713433 (5 : ZMod 229713433)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (59, 1), (12479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (59, 1), (12479, 1)] : List FactorBlock).map factorBlockValue).prod) = 229713433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_fourteenL_12479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 229713433) ^ 114856716 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 76571144 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 17670264 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 3893448 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 18408 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_238569407 : Nat.Prime 238569407 := by
  apply lucas_primality 238569407 (5 : ZMod 238569407)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (2909383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (2909383, 1)] : List FactorBlock).map factorBlockValue).prod) = 238569407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_fourteenL_2909383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 238569407) ^ 119284703 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 238569407) ^ 5818766 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 238569407) ^ 82 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_267586283 : Nat.Prime 267586283 := by
  apply lucas_primality 267586283 (2 : ZMod 267586283)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (679153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (679153, 1)] : List FactorBlock).map factorBlockValue).prod) = 267586283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_197
      · exact prime_fourteenL_679153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 267586283) ^ 133793141 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 267586283) ^ 1358306 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 267586283) ^ 394 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_286464551 : Nat.Prime 286464551 := by
  apply lucas_primality 286464551 (7 : ZMod 286464551)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 286464551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_1303
      · exact prime_fourteenL_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 286464551) ^ 143232275 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 57292910 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 219850 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 65150 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_299676301 : Nat.Prime 299676301 := by
  apply lucas_primality 299676301 (10 : ZMod 299676301)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (11, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (11, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) = 299676301 - 1 by
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
      · exact prime_fourteenL_12973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 299676301) ^ 149838150 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 299676301) ^ 99892100 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 299676301) ^ 59935260 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 299676301) ^ 42810900 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 299676301) ^ 27243300 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 299676301) ^ 23100 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_312242717 : Nat.Prime 312242717 := by
  apply lucas_primality 312242717 (2 : ZMod 312242717)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (53, 1), (35923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (53, 1), (35923, 1)] : List FactorBlock).map factorBlockValue).prod) = 312242717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_53
      · exact prime_fourteenL_35923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 312242717) ^ 156121358 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 312242717) ^ 7615676 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 312242717) ^ 5891372 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 312242717) ^ 8692 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_343451299 : Nat.Prime 343451299 := by
  apply lucas_primality 343451299 (2 : ZMod 343451299)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4327, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4327, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod) = 343451299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_4327
      · exact prime_fourteenL_13229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 343451299) ^ 171725649 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 343451299) ^ 114483766 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 343451299) ^ 79374 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 343451299) ^ 25962 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_381350491 : Nat.Prime 381350491 := by
  apply lucas_primality 381350491 (2 : ZMod 381350491)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) = 381350491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_fourteenL_343559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381350491) ^ 190675245 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 127116830 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 76270098 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 10306770 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 1110 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_453380897 : Nat.Prime 453380897 := by
  apply lucas_primality 453380897 (3 : ZMod 453380897)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (257, 1), (1901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (257, 1), (1901, 1)] : List FactorBlock).map factorBlockValue).prod) = 453380897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_fourteenL_257
      · exact prime_fourteenL_1901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 453380897) ^ 226690448 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 453380897) ^ 15633824 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 453380897) ^ 1764128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 453380897) ^ 238496 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_fourteenL_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_567315271 : Nat.Prime 567315271 := by
  apply lucas_primality 567315271 (3 : ZMod 567315271)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (6303503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (6303503, 1)] : List FactorBlock).map factorBlockValue).prod) = 567315271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_6303503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 567315271) ^ 283657635 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 567315271) ^ 189105090 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 567315271) ^ 113463054 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 567315271) ^ 90 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_757865809 : Nat.Prime 757865809 := by
  apply lucas_primality 757865809 (22 : ZMod 757865809)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (7, 1), (139, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (7, 1), (139, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) = 757865809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_139
      · exact prime_fourteenL_601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 757865809) ^ 378932904 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 757865809) ^ 252621936 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 757865809) ^ 108266544 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 757865809) ^ 5452272 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 757865809) ^ 1261008 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_760771409 : Nat.Prime 760771409 := by
  apply lucas_primality 760771409 (3 : ZMod 760771409)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (499, 1), (95287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (499, 1), (95287, 1)] : List FactorBlock).map factorBlockValue).prod) = 760771409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_499
      · exact prime_fourteenL_95287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 760771409) ^ 380385704 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 760771409) ^ 1524592 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 760771409) ^ 7984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_771140911 : Nat.Prime 771140911 := by
  apply lucas_primality 771140911 (6 : ZMod 771140911)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (1512041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (1512041, 1)] : List FactorBlock).map factorBlockValue).prod) = 771140911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_fourteenL_1512041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 771140911) ^ 385570455 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 771140911) ^ 257046970 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 771140911) ^ 154228182 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 771140911) ^ 45361230 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 771140911) ^ 510 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_811821761 : Nat.Prime 811821761 := by
  apply lucas_primality 811821761 (3 : ZMod 811821761)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (2536943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (2536943, 1)] : List FactorBlock).map factorBlockValue).prod) = 811821761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_2536943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 811821761) ^ 405910880 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 811821761) ^ 162364352 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 811821761) ^ 320 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_879258253 : Nat.Prime 879258253 := by
  apply lucas_primality 879258253 (2 : ZMod 879258253)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73271521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73271521, 1)] : List FactorBlock).map factorBlockValue).prod) = 879258253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_73271521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 879258253) ^ 439629126 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 879258253) ^ 293086084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 879258253) ^ 12 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_938870431 : Nat.Prime 938870431 := by
  apply lucas_primality 938870431 (7 : ZMod 938870431)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod) = 938870431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_fourteenL_292483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 938870431) ^ 469435215 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 312956810 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 187774086 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 8774490 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 3210 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1088310731 : Nat.Prime 1088310731 := by
  apply lucas_primality 1088310731 (7 : ZMod 1088310731)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088310731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_fourteenL_2239
      · exact prime_t64_3739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1088310731) ^ 544155365 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 217662146 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 83716210 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 486070 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 291070 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1396950757 : Nat.Prime 1396950757 := by
  apply lucas_primality 1396950757 (2 : ZMod 1396950757)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (83, 1), (73819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (83, 1), (73819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1396950757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_83
      · exact prime_fourteenL_73819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1396950757) ^ 698475378 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1396950757) ^ 465650252 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1396950757) ^ 73523724 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1396950757) ^ 16830732 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1396950757) ^ 18924 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1462090577 : Nat.Prime 1462090577 := by
  apply lucas_primality 1462090577 (6 : ZMod 1462090577)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1462090577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_89
      · exact prime_fourteenL_60397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1462090577) ^ 731045288 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 86005328 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 16427984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 24208 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1514175419 : Nat.Prime 1514175419 := by
  apply lucas_primality 1514175419 (2 : ZMod 1514175419)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (239, 1), (452533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (239, 1), (452533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514175419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_239
      · exact prime_fourteenL_452533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1514175419) ^ 757087709 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 216310774 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 6335462 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 3346 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1577676713 : Nat.Prime 1577676713 := by
  apply lucas_primality 1577676713 (3 : ZMod 1577676713)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (197209589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (197209589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1577676713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_197209589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1577676713) ^ 788838356 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1577676713) ^ 8 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_fourteenL_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1853147981 : Nat.Prime 1853147981 := by
  apply lucas_primality 1853147981 (2 : ZMod 1853147981)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (107, 1), (865957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (107, 1), (865957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1853147981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_fourteenL_865957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1853147981) ^ 926573990 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853147981) ^ 370629596 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853147981) ^ 17319140 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853147981) ^ 2140 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_2477599469 : Nat.Prime 2477599469 := by
  apply lucas_primality 2477599469 (2 : ZMod 2477599469)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (23, 1), (83, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (23, 1), (83, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2477599469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_83
      · exact prime_fourteenL_17077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2477599469) ^ 1238799734 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477599469) ^ 130399972 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477599469) ^ 107721716 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477599469) ^ 29850596 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477599469) ^ 145084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_2828894209 : Nat.Prime 2828894209 := by
  apply lucas_primality 2828894209 (13 : ZMod 2828894209)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 15), (3, 1), (7, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 15), (3, 1), (7, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 2828894209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_fourteenL_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2828894209) ^ 1414447104 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 2828894209) ^ 942964736 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 2828894209) ^ 404127744 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 2828894209) ^ 688128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_359
      · exact prime_fourteenL_677
      · exact prime_fourteenL_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3813504911 : Nat.Prime 3813504911 := by
  apply lucas_primality 3813504911 (17 : ZMod 3813504911)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3813504911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_381350491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3813504911) ^ 1906752455 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 762700982 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 10 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3911415413 : Nat.Prime 3911415413 := by
  apply lucas_primality 3911415413 (2 : ZMod 3911415413)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3911415413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1069
      · exact prime_fourteenL_914737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3911415413) ^ 1955707706 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 3658948 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 4276 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_4225305743 : Nat.Prime 4225305743 := by
  apply lucas_primality 4225305743 (5 : ZMod 4225305743)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (2393, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (2393, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4225305743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_fourteenL_2393
      · exact prime_fourteenL_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4225305743) ^ 2112652871 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 603615106 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 145700198 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 1765694 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 971558 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_4794820817 : Nat.Prime 4794820817 := by
  apply lucas_primality 4794820817 (3 : ZMod 4794820817)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (299676301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (299676301, 1)] : List FactorBlock).map factorBlockValue).prod) = 4794820817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_299676301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4794820817) ^ 2397410408 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4794820817) ^ 16 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_5484812849 : Nat.Prime 5484812849 := by
  apply lucas_primality 5484812849 (3 : ZMod 5484812849)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5573, 1), (61511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5573, 1), (61511, 1)] : List FactorBlock).map factorBlockValue).prod) = 5484812849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_5573
      · exact prime_fourteenL_61511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5484812849) ^ 2742406424 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484812849) ^ 984176 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484812849) ^ 89168 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_5741877473 : Nat.Prime 5741877473 := by
  apply lucas_primality 5741877473 (3 : ZMod 5741877473)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (101, 1), (43331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (101, 1), (43331, 1)] : List FactorBlock).map factorBlockValue).prod) = 5741877473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_101
      · exact prime_fourteenL_43331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5741877473) ^ 2870938736 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 140045792 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 56850272 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 132512 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7436904037 : Nat.Prime 7436904037 := by
  apply lucas_primality 7436904037 (2 : ZMod 7436904037)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7541, 1), (82183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7541, 1), (82183, 1)] : List FactorBlock).map factorBlockValue).prod) = 7436904037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_7541
      · exact prime_fourteenL_82183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7436904037) ^ 3718452018 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7436904037) ^ 2478968012 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7436904037) ^ 986196 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7436904037) ^ 90492 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7652554093 : Nat.Prime 7652554093 := by
  apply lucas_primality 7652554093 (5 : ZMod 7652554093)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) = 7652554093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_71
      · exact prime_fourteenL_2993957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7652554093) ^ 3826277046 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2550851364 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 107782452 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2556 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_fourteenL_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_11118887887 : Nat.Prime 11118887887 := by
  apply lucas_primality 11118887887 (3 : ZMod 11118887887)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1853147981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1853147981, 1)] : List FactorBlock).map factorBlockValue).prod) = 11118887887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_1853147981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11118887887) ^ 5559443943 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11118887887) ^ 3706295962 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11118887887) ^ 6 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_14853048211 : Nat.Prime 14853048211 := by
  apply lucas_primality 14853048211 (2 : ZMod 14853048211)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 14853048211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_fourteenL_173
      · exact prime_fourteenL_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14853048211) ^ 7426524105 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 4951016070 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2970609642 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2121864030 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1350277110 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1142542170 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 85855770 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 15585570 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_16539367177 : Nat.Prime 16539367177 := by
  apply lucas_primality 16539367177 (5 : ZMod 16539367177)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (229713433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (229713433, 1)] : List FactorBlock).map factorBlockValue).prod) = 16539367177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_229713433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16539367177) ^ 8269683588 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 16539367177) ^ 5513122392 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 16539367177) ^ 72 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_17037864143 : Nat.Prime 17037864143 := by
  apply lucas_primality 17037864143 (5 : ZMod 17037864143)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) = 17037864143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_fourteenL_709
      · exact prime_fourteenL_22543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17037864143) ^ 8518932071 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 1310604934 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 415557662 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 24030838 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 755794 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_20319607769 : Nat.Prime 20319607769 := by
  apply lucas_primality 20319607769 (3 : ZMod 20319607769)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) = 20319607769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_5881
      · exact prime_fourteenL_431891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20319607769) ^ 10159803884 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 3455128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 47048 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_23463297631 : Nat.Prime 23463297631 := by
  apply lucas_primality 23463297631 (6 : ZMod 23463297631)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (14449, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (14449, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod) = 23463297631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_14449
      · exact prime_fourteenL_18043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23463297631) ^ 11731648815 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 7821099210 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 4692659526 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 1623870 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 1300410 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_24079071829 : Nat.Prime 24079071829 := by
  apply lucas_primality 24079071829 (2 : ZMod 24079071829)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (8287, 1), (34591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (8287, 1), (34591, 1)] : List FactorBlock).map factorBlockValue).prod) = 24079071829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_fourteenL_8287
      · exact prime_fourteenL_34591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24079071829) ^ 12039535914 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 8026357276 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 3439867404 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 2905644 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 696108 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_487
      · exact prime_fourteenL_2621
      · exact prime_fourteenL_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_29245518173 : Nat.Prime 29245518173 := by
  apply lucas_primality 29245518173 (5 : ZMod 29245518173)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (31, 1), (18142381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (31, 1), (18142381, 1)] : List FactorBlock).map factorBlockValue).prod) = 29245518173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_fourteenL_18142381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29245518173) ^ 14622759086 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 2249655244 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 943403812 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 1612 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_33946730509 : Nat.Prime 33946730509 := by
  apply lucas_primality 33946730509 (2 : ZMod 33946730509)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2828894209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2828894209, 1)] : List FactorBlock).map factorBlockValue).prod) = 33946730509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_2828894209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33946730509) ^ 16973365254 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 33946730509) ^ 11315576836 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 33946730509) ^ 12 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_36033175631 : Nat.Prime 36033175631 := by
  apply lucas_primality 36033175631 (13 : ZMod 36033175631)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (156665981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (156665981, 1)] : List FactorBlock).map factorBlockValue).prod) = 36033175631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_fourteenL_156665981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 36033175631) ^ 18016587815 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36033175631) ^ 7206635126 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36033175631) ^ 1566659810 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36033175631) ^ 230 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_39181973737 : Nat.Prime 39181973737 := by
  apply lucas_primality 39181973737 (5 : ZMod 39181973737)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (41, 1), (103, 1), (20347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (41, 1), (103, 1), (20347, 1)] : List FactorBlock).map factorBlockValue).prod) = 39181973737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_41
      · exact prime_t64_103
      · exact prime_fourteenL_20347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39181973737) ^ 19590986868 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 39181973737) ^ 13060657912 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 39181973737) ^ 2062209144 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 39181973737) ^ 955657896 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 39181973737) ^ 380407512 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 39181973737) ^ 1925688 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_47479945663 : Nat.Prime 47479945663 := by
  apply lucas_primality 47479945663 (3 : ZMod 47479945663)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (879258253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (879258253, 1)] : List FactorBlock).map factorBlockValue).prod) = 47479945663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_879258253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47479945663) ^ 23739972831 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 47479945663) ^ 15826648554 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 47479945663) ^ 54 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_70908014633 : Nat.Prime 70908014633 := by
  apply lucas_primality 70908014633 (3 : ZMod 70908014633)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod) = 70908014633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_fourteenL_4919
      · exact prime_fourteenL_19801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70908014633) ^ 35454007316 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 10129716376 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 5454462664 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 14415128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 3581032 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_73
      · exact prime_fourteenL_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_81554969011 : Nat.Prime 81554969011 := by
  apply lucas_primality 81554969011 (3 : ZMod 81554969011)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) = 81554969011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_fourteenL_143078893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81554969011) ^ 40777484505 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 27184989670 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 16310993802 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 4292366790 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 570 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_84927410431 : Nat.Prime 84927410431 := by
  apply lucas_primality 84927410431 (6 : ZMod 84927410431)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) = 84927410431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_t64_67
      · exact prime_fourteenL_692663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 84927410431) ^ 42463705215 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 28309136810 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 16985482086 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1392252630 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1267573290 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 122610 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_101995373461 : Nat.Prime 101995373461 := by
  apply lucas_primality 101995373461 (2 : ZMod 101995373461)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (643, 1), (2643737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (643, 1), (2643737, 1)] : List FactorBlock).map factorBlockValue).prod) = 101995373461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_643
      · exact prime_fourteenL_2643737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101995373461) ^ 50997686730 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 33998457820 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 20399074692 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 158624220 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 38580 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_102310987907 : Nat.Prime 102310987907 := by
  apply lucas_primality 102310987907 (2 : ZMod 102310987907)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 102310987907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_fourteenL_7013
      · exact prime_fourteenL_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102310987907) ^ 51155493953 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 4448303822 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 14588762 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 7419754 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_119543144893 : Nat.Prime 119543144893 := by
  apply lucas_primality 119543144893 (2 : ZMod 119543144893)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod) = 119543144893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_fourteenL_6271
      · exact prime_fourteenL_83609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119543144893) ^ 59771572446 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 39847714964 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 6291744468 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 19062852 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 1429788 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_439
      · exact prime_fourteenL_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_144222292169 : Nat.Prime 144222292169 := by
  apply lucas_primality 144222292169 (3 : ZMod 144222292169)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131, 1), (137616691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131, 1), (137616691, 1)] : List FactorBlock).map factorBlockValue).prod) = 144222292169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_131
      · exact prime_fourteenL_137616691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144222292169) ^ 72111146084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 144222292169) ^ 1100933528 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 144222292169) ^ 1048 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_152394958517 : Nat.Prime 152394958517 := by
  apply lucas_primality 152394958517 (2 : ZMod 152394958517)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) = 152394958517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_593
      · exact prime_fourteenL_709
      · exact prime_fourteenL_90617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152394958517) ^ 76197479258 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 256989812 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 214943524 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 1681748 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_210091982543 : Nat.Prime 210091982543 := by
  apply lucas_primality 210091982543 (5 : ZMod 210091982543)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (349, 1), (23153183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (349, 1), (23153183, 1)] : List FactorBlock).map factorBlockValue).prod) = 210091982543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_349
      · exact prime_fourteenL_23153183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 210091982543) ^ 105045991271 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 16160921734 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 601982758 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 9074 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_211265287151 : Nat.Prime 211265287151 := by
  apply lucas_primality 211265287151 (7 : ZMod 211265287151)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4225305743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4225305743, 1)] : List FactorBlock).map factorBlockValue).prod) = 211265287151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_4225305743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 211265287151) ^ 105632643575 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 211265287151) ^ 42253057430 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 211265287151) ^ 50 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_277280084413 : Nat.Prime 277280084413 := by
  apply lucas_primality 277280084413 (5 : ZMod 277280084413)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod) = 277280084413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_fourteenL_3600853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 277280084413) ^ 138640042206 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 92426694804 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 12055655844 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 8944518852 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 77004 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_282910655971 : Nat.Prime 282910655971 := by
  apply lucas_primality 282910655971 (2 : ZMod 282910655971)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (16943, 1), (185531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (16943, 1), (185531, 1)] : List FactorBlock).map factorBlockValue).prod) = 282910655971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_16943
      · exact prime_fourteenL_185531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 282910655971) ^ 141455327985 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282910655971) ^ 94303551990 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282910655971) ^ 56582131194 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282910655971) ^ 16697790 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282910655971) ^ 1524870 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_326767060643 : Nat.Prime 326767060643 := by
  apply lucas_primality 326767060643 (2 : ZMod 326767060643)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) = 326767060643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_fourteenL_14853048211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 326767060643) ^ 163383530321 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 29706096422 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 22 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_363715041847 : Nat.Prime 363715041847 := by
  apply lucas_primality 363715041847 (5 : ZMod 363715041847)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (283, 1), (16477079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (283, 1), (16477079, 1)] : List FactorBlock).map factorBlockValue).prod) = 363715041847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_283
      · exact prime_fourteenL_16477079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 363715041847) ^ 181857520923 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 363715041847) ^ 121238347282 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 363715041847) ^ 27978080142 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 363715041847) ^ 1285212162 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 363715041847) ^ 22074 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_553402018259 : Nat.Prime 553402018259 := by
  apply lucas_primality 553402018259 (2 : ZMod 553402018259)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1613, 1), (2011, 1), (85303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1613, 1), (2011, 1), (85303, 1)] : List FactorBlock).map factorBlockValue).prod) = 553402018259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1613
      · exact prime_fourteenL_2011
      · exact prime_fourteenL_85303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 553402018259) ^ 276701009129 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 553402018259) ^ 343088666 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 553402018259) ^ 275187478 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 553402018259) ^ 6487486 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_852391097893 : Nat.Prime 852391097893 := by
  apply lucas_primality 852391097893 (2 : ZMod 852391097893)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) = 852391097893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_853
      · exact prime_fourteenL_27757949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 852391097893) ^ 426195548946 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 284130365964 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 999286164 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 30708 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_977519457737 : Nat.Prime 977519457737 := by
  apply lucas_primality 977519457737 (3 : ZMod 977519457737)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) = 977519457737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1259
      · exact prime_fourteenL_3643
      · exact prime_fourteenL_26641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 977519457737) ^ 488759728868 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 776425304 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 268328152 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 36692296 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_999086680303 : Nat.Prime 999086680303 := by
  apply lucas_primality 999086680303 (5 : ZMod 999086680303)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (5741877473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (5741877473, 1)] : List FactorBlock).map factorBlockValue).prod) = 999086680303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_fourteenL_5741877473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 999086680303) ^ 499543340151 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 333028893434 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 34451264838 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 174 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1026349089653 : Nat.Prime 1026349089653 := by
  apply lucas_primality 1026349089653 (2 : ZMod 1026349089653)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026349089653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1223
      · exact prime_fourteenL_209801531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1026349089653) ^ 513174544826 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 839206124 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 4892 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1534406528407 : Nat.Prime 1534406528407 := by
  apply lucas_primality 1534406528407 (5 : ZMod 1534406528407)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (11118887887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (11118887887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1534406528407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_fourteenL_11118887887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1534406528407) ^ 767203264203 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1534406528407) ^ 511468842802 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1534406528407) ^ 66713327322 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1534406528407) ^ 138 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1686291654781 : Nat.Prime 1686291654781 := by
  apply lucas_primality 1686291654781 (2 : ZMod 1686291654781)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod) = 1686291654781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_131
      · exact prime_t64_193
      · exact prime_fourteenL_370537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1686291654781) ^ 843145827390 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 562097218260 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 337258330956 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 12872455380 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 8737262460 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 4550940 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_2182290251083 : Nat.Prime 2182290251083 := by
  apply lucas_primality 2182290251083 (2 : ZMod 2182290251083)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (363715041847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (363715041847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2182290251083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_363715041847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2182290251083) ^ 1091145125541 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2182290251083) ^ 727430083694 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2182290251083) ^ 6 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3433626695693 : Nat.Prime 3433626695693 := by
  apply lucas_primality 3433626695693 (2 : ZMod 3433626695693)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (45949, 1), (812249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (45949, 1), (812249, 1)] : List FactorBlock).map factorBlockValue).prod) = 3433626695693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_fourteenL_45949
      · exact prime_fourteenL_812249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3433626695693) ^ 1716813347846 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3433626695693) ^ 149288117204 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3433626695693) ^ 74726908 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3433626695693) ^ 4227308 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_4405180062253 : Nat.Prime 4405180062253 := by
  apply lucas_primality 4405180062253 (6 : ZMod 4405180062253)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod) = 4405180062253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_fourteenL_938870431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4405180062253) ^ 2202590031126 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 1468393354084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 259128238956 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 191529567924 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 4692 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_5915731660739 : Nat.Prime 5915731660739 := by
  apply lucas_primality 5915731660739 (2 : ZMod 5915731660739)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (101995373461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (101995373461, 1)] : List FactorBlock).map factorBlockValue).prod) = 5915731660739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_fourteenL_101995373461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5915731660739) ^ 2957865830369 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915731660739) ^ 203990746922 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915731660739) ^ 58 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7007144209529 : Nat.Prime 7007144209529 := by
  apply lucas_primality 7007144209529 (3 : ZMod 7007144209529)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) = 7007144209529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_112573
      · exact prime_fourteenL_7780667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7007144209529) ^ 3503572104764 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 62245336 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 900584 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7121991849451 : Nat.Prime 7121991849451 := by
  apply lucas_primality 7121991849451 (3 : ZMod 7121991849451)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (47479945663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (47479945663, 1)] : List FactorBlock).map factorBlockValue).prod) = 7121991849451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_47479945663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7121991849451) ^ 3560995924725 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 2373997283150 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 1424398369890 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 150 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_9319916197373 : Nat.Prime 9319916197373 := by
  apply lucas_primality 9319916197373 (2 : ZMod 9319916197373)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (37, 1), (197, 1), (29059717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (37, 1), (197, 1), (29059717, 1)] : List FactorBlock).map factorBlockValue).prod) = 9319916197373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_37
      · exact prime_t64_197
      · exact prime_fourteenL_29059717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9319916197373) ^ 4659958098686 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9319916197373) ^ 847265108852 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9319916197373) ^ 251889626956 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9319916197373) ^ 47309219276 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9319916197373) ^ 320716 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_9427522870043 : Nat.Prime 9427522870043 := by
  apply lucas_primality 9427522870043 (2 : ZMod 9427522870043)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod) = 9427522870043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_fourteenL_277280084413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9427522870043) ^ 4713761435021 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 554560168826 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 34 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_10429204246537 : Nat.Prime 10429204246537 := by
  apply lucas_primality 10429204246537 (7 : ZMod 10429204246537)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 2), (36575219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 2), (36575219, 1)] : List FactorBlock).map factorBlockValue).prod) = 10429204246537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_109
      · exact prime_fourteenL_36575219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10429204246537) ^ 5214602123268 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 10429204246537) ^ 3476401415512 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 10429204246537) ^ 95680772904 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 10429204246537) ^ 285144 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_11241906997859 : Nat.Prime 11241906997859 := by
  apply lucas_primality 11241906997859 (2 : ZMod 11241906997859)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (224897, 1), (24993457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (224897, 1), (24993457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11241906997859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_224897
      · exact prime_fourteenL_24993457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11241906997859) ^ 5620953498929 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11241906997859) ^ 49986914 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11241906997859) ^ 449794 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_fourteenL_971
      · exact prime_fourteenL_1031
      · exact prime_fourteenL_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_14785332476099 : Nat.Prime 14785332476099 := by
  apply lucas_primality 14785332476099 (2 : ZMod 14785332476099)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (565997, 1), (13061317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (565997, 1), (13061317, 1)] : List FactorBlock).map factorBlockValue).prod) = 14785332476099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_565997
      · exact prime_fourteenL_13061317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14785332476099) ^ 7392666238049 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14785332476099) ^ 26122634 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14785332476099) ^ 1131994 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_19900477325279 : Nat.Prime 19900477325279 := by
  apply lucas_primality 19900477325279 (13 : ZMod 19900477325279)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2897, 1), (312242717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2897, 1), (312242717, 1)] : List FactorBlock).map factorBlockValue).prod) = 19900477325279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_2897
      · exact prime_fourteenL_312242717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 19900477325279) ^ 9950238662639 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 19900477325279) ^ 1809134302298 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 19900477325279) ^ 6869339774 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 19900477325279) ^ 63734 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_t64_97
      · exact prime_fourteenL_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_27346626158783 : Nat.Prime 27346626158783 := by
  apply lucas_primality 27346626158783 (5 : ZMod 27346626158783)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) = 27346626158783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_fourteenL_84927410431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27346626158783) ^ 13673313079391 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 3906660879826 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 1188983746034 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 322 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_fourteenL_293
      · exact prime_t64_317
      · exact prime_fourteenL_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_101
      · exact prime_fourteenL_5779
      · exact prime_fourteenL_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_601
      · exact prime_fourteenL_1069
      · exact prime_fourteenL_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_46558229274047 : Nat.Prime 46558229274047 := by
  apply lucas_primality 46558229274047 (7 : ZMod 46558229274047)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) = 46558229274047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_fourteenL_151939
      · exact prime_fourteenL_951637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 46558229274047) ^ 23279114637023 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 6651175610578 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 2024270838002 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 306427114 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 48924358 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_54969851117647 : Nat.Prime 54969851117647 := by
  apply lucas_primality 54969851117647 (3 : ZMod 54969851117647)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24977, 1), (122267711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24977, 1), (122267711, 1)] : List FactorBlock).map factorBlockValue).prod) = 54969851117647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_24977
      · exact prime_fourteenL_122267711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54969851117647) ^ 27484925558823 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54969851117647) ^ 18323283705882 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54969851117647) ^ 2200818798 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54969851117647) ^ 449586 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_76896872970083 : Nat.Prime 76896872970083 := by
  apply lucas_primality 76896872970083 (5 : ZMod 76896872970083)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (953, 1), (1543, 1), (2376989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (953, 1), (1543, 1), (2376989, 1)] : List FactorBlock).map factorBlockValue).prod) = 76896872970083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_fourteenL_953
      · exact prime_fourteenL_1543
      · exact prime_fourteenL_2376989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76896872970083) ^ 38448436485041 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 76896872970083) ^ 6990624815462 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 76896872970083) ^ 80689268594 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 76896872970083) ^ 49835951374 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 76896872970083) ^ 32350538 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_89405586621479 : Nat.Prime 89405586621479 := by
  apply lucas_primality 89405586621479 (7 : ZMod 89405586621479)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (113, 1), (39227, 1), (325319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (113, 1), (39227, 1), (325319, 1)] : List FactorBlock).map factorBlockValue).prod) = 89405586621479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_113
      · exact prime_fourteenL_39227
      · exact prime_fourteenL_325319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 89405586621479) ^ 44702793310739 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 2884051181338 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 791199881606 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 2279184914 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 274824362 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_130207195769087 : Nat.Prime 130207195769087 := by
  apply lucas_primality 130207195769087 (5 : ZMod 130207195769087)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (1447, 1), (343451299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (1447, 1), (343451299, 1)] : List FactorBlock).map factorBlockValue).prod) = 130207195769087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_131
      · exact prime_fourteenL_1447
      · exact prime_fourteenL_343451299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 130207195769087) ^ 65103597884543 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130207195769087) ^ 993948059306 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130207195769087) ^ 89984240338 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130207195769087) ^ 379114 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_135096519595393 : Nat.Prime 135096519595393 := by
  apply lucas_primality 135096519595393 (10 : ZMod 135096519595393)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) = 135096519595393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_275491
      · exact prime_fourteenL_425681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 135096519595393) ^ 67548259797696 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 45032173198464 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 490384512 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 317365632 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_144825599360927 : Nat.Prime 144825599360927 := by
  apply lucas_primality 144825599360927 (5 : ZMod 144825599360927)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2657, 1), (2477599469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2657, 1), (2477599469, 1)] : List FactorBlock).map factorBlockValue).prod) = 144825599360927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_fourteenL_2657
      · exact prime_fourteenL_2477599469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 144825599360927) ^ 72412799680463 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 144825599360927) ^ 13165963578266 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 144825599360927) ^ 54507188318 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 144825599360927) ^ 58454 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_415034571917257 : Nat.Prime 415034571917257 := by
  apply lucas_primality 415034571917257 (5 : ZMod 415034571917257)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) = 415034571917257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_59
      · exact prime_fourteenL_13331
      · exact prime_fourteenL_758159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 415034571917257) ^ 207517285958628 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 138344857305752 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 14311536962664 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 7034484269784 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 31133041176 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 547424184 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_556509832673117 : Nat.Prime 556509832673117 := by
  apply lucas_primality 556509832673117 (2 : ZMod 556509832673117)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (193, 1), (229, 1), (2357, 1), (190793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (193, 1), (229, 1), (2357, 1), (190793, 1)] : List FactorBlock).map factorBlockValue).prod) = 556509832673117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_193
      · exact prime_t64_229
      · exact prime_fourteenL_2357
      · exact prime_fourteenL_190793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 556509832673117) ^ 278254916336558 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 79501404667588 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2883470635612 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2430173941804 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 236109390188 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2916825212 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_t64_233
      · exact prime_t64_409
      · exact prime_fourteenL_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_659702079143411 : Nat.Prime 659702079143411 := by
  apply lucas_primality 659702079143411 (2 : ZMod 659702079143411)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) = 659702079143411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_230291
      · exact prime_fourteenL_286464551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 659702079143411) ^ 329851039571705 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 131940415828682 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2864645510 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2302910 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_223
      · exact prime_t64_283
      · exact prime_fourteenL_5843
      · exact prime_fourteenL_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_854639021934121 : Nat.Prime 854639021934121 := by
  apply lucas_primality 854639021934121 (11 : ZMod 854639021934121)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7121991849451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7121991849451, 1)] : List FactorBlock).map factorBlockValue).prod) = 854639021934121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_7121991849451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 854639021934121) ^ 427319510967060 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 284879673978040 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 170927804386824 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 120 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_894812899362253 : Nat.Prime 894812899362253 := by
  apply lucas_primality 894812899362253 (5 : ZMod 894812899362253)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (101, 1), (3907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (101, 1), (3907, 1)] : List FactorBlock).map factorBlockValue).prod) = 894812899362253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_101
      · exact prime_fourteenL_3907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 894812899362253) ^ 447406449681126 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 298270966454084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 68831761489404 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 47095415755908 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 38904908667924 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 30855617219388 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 28864932237492 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 24184132415196 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 8859533657052 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 894812899362253) ^ 229028128836 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1583581521533941 : Nat.Prime 1583581521533941 := by
  apply lucas_primality 1583581521533941 (2 : ZMod 1583581521533941)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583581521533941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_fourteenL_977519457737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1583581521533941) ^ 791790760766970 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 527860507177980 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 316716304306788 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 1620 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_4501364654091139 : Nat.Prime 4501364654091139 := by
  apply lucas_primality 4501364654091139 (2 : ZMod 4501364654091139)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (359, 1), (7436904037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (359, 1), (7436904037, 1)] : List FactorBlock).map factorBlockValue).prod) = 4501364654091139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_281
      · exact prime_fourteenL_359
      · exact prime_fourteenL_7436904037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4501364654091139) ^ 2250682327045569 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4501364654091139) ^ 1500454884697046 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4501364654091139) ^ 16019091295698 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4501364654091139) ^ 12538620206382 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4501364654091139) ^ 605274 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_6933661561302821 : Nat.Prime 6933661561302821 := by
  apply lucas_primality 6933661561302821 (2 : ZMod 6933661561302821)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (999086680303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (999086680303, 1)] : List FactorBlock).map factorBlockValue).prod) = 6933661561302821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_fourteenL_347
      · exact prime_fourteenL_999086680303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6933661561302821) ^ 3466830780651410 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 1386732312260564 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 19981733606060 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 6940 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_8233825701109243 : Nat.Prime 8233825701109243 := by
  apply lucas_primality 8233825701109243 (2 : ZMod 8233825701109243)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (967, 1), (1327, 1), (8219, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (967, 1), (1327, 1), (8219, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) = 8233825701109243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_fourteenL_967
      · exact prime_fourteenL_1327
      · exact prime_fourteenL_8219
      · exact prime_fourteenL_10009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8233825701109243) ^ 4116912850554621 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 2744608567036414 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 633371207777634 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 8514814582326 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 6204842276646 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 1001803832718 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8233825701109243) ^ 822642192138 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_8438917837893001 : Nat.Prime 8438917837893001 := by
  apply lucas_primality 8438917837893001 (11 : ZMod 8438917837893001)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (59, 1), (40433, 1), (1179173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (59, 1), (40433, 1), (1179173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8438917837893001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_59
      · exact prime_fourteenL_40433
      · exact prime_fourteenL_1179173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8438917837893001) ^ 4219458918946500 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 2812972612631000 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 1687783567578600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 143032505727000 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 208713621000 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 7156641000 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_16877197084131511 : Nat.Prime 16877197084131511 := by
  apply lucas_primality 16877197084131511 (6 : ZMod 16877197084131511)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) = 16877197084131511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_t64_89
      · exact prime_fourteenL_17037864143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16877197084131511) ^ 8438598542065755 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 5625732361377170 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 3375439416826302 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 2411028154875930 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 318437680832670 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 189631427911590 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 990570 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_20660407174714891 : Nat.Prime 20660407174714891 := by
  apply lucas_primality 20660407174714891 (2 : ZMod 20660407174714891)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) = 20660407174714891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_61
      · exact prime_fourteenL_1026349089653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20660407174714891) ^ 10330203587357445 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 6886802391571630 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 4132081434942978 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 1878218834064990 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 338695199585490 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 20130 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_21292507748726713 : Nat.Prime 21292507748726713 := by
  apply lucas_primality 21292507748726713 (5 : ZMod 21292507748726713)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (241, 1), (93199, 1), (13166369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (241, 1), (93199, 1), (13166369, 1)] : List FactorBlock).map factorBlockValue).prod) = 21292507748726713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_241
      · exact prime_fourteenL_93199
      · exact prime_fourteenL_13166369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21292507748726713) ^ 10646253874363356 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 7097502582908904 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 88350654559032 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 228462834888 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 1617189048 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_t64_163
      · exact prime_fourteenL_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_28569770566964843 : Nat.Prime 28569770566964843 := by
  apply lucas_primality 28569770566964843 (2 : ZMod 28569770566964843)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (34897, 1), (24079071829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (34897, 1), (24079071829, 1)] : List FactorBlock).map factorBlockValue).prod) = 28569770566964843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_fourteenL_34897
      · exact prime_fourteenL_24079071829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28569770566964843) ^ 14284885283482421 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 1680574739233226 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 818688442186 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 1186498 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_97937826197793863 : Nat.Prime 97937826197793863 := by
  apply lucas_primality 97937826197793863 (5 : ZMod 97937826197793863)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) = 97937826197793863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_t64_167
      · exact prime_fourteenL_316097
      · exact prime_fourteenL_1489003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97937826197793863) ^ 48968913098896931 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 13991118028256266 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 1100425013458358 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 586454049088586 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 309834722246 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 65774095954 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_114218290024018991 : Nat.Prime 114218290024018991 := by
  apply lucas_primality 114218290024018991 (17 : ZMod 114218290024018991)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) = 114218290024018991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_491
      · exact prime_fourteenL_2677
      · exact prime_fourteenL_15073
      · exact prime_fourteenL_576509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 114218290024018991) ^ 57109145012009495 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 22843658004803798 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 232623808602890 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 42666525970870 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 7577674651630 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 198120567110 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_116325676917092891 : Nat.Prime 116325676917092891 := by
  apply lucas_primality 116325676917092891 (2 : ZMod 116325676917092891)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (894812899362253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (894812899362253, 1)] : List FactorBlock).map factorBlockValue).prod) = 116325676917092891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_fourteenL_894812899362253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116325676917092891) ^ 58162838458546445 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116325676917092891) ^ 23265135383418578 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116325676917092891) ^ 8948128993622530 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 116325676917092891) ^ 130 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_130278547148823391 : Nat.Prime 130278547148823391 := by
  apply lucas_primality 130278547148823391 (6 : ZMod 130278547148823391)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (54969851117647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (54969851117647, 1)] : List FactorBlock).map factorBlockValue).prod) = 130278547148823391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_fourteenL_54969851117647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 130278547148823391) ^ 65139273574411695 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 130278547148823391) ^ 43426182382941130 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 130278547148823391) ^ 26055709429764678 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 130278547148823391) ^ 1649095533529410 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 130278547148823391) ^ 2370 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_138042225743563577 : Nat.Prime 138042225743563577 := by
  apply lucas_primality 138042225743563577 (3 : ZMod 138042225743563577)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (193, 1), (89405586621479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (193, 1), (89405586621479, 1)] : List FactorBlock).map factorBlockValue).prod) = 138042225743563577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_193
      · exact prime_fourteenL_89405586621479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138042225743563577) ^ 69021112871781788 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 138042225743563577) ^ 715244692971832 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 138042225743563577) ^ 1544 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_158361893331124207 : Nat.Prime 158361893331124207 := by
  apply lucas_primality 158361893331124207 (5 : ZMod 158361893331124207)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) = 158361893331124207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_97
      · exact prime_fourteenL_10049639
      · exact prime_fourteenL_27075547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158361893331124207) ^ 79180946665562103 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 52787297777041402 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 1632596838465198 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 15757968354 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 5848889898 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_79
      · exact prime_fourteenL_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1050564897764164459 : Nat.Prime 1050564897764164459 := by
  apply lucas_primality 1050564897764164459 (2 : ZMod 1050564897764164459)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (31, 1), (144825599360927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (31, 1), (144825599360927, 1)] : List FactorBlock).map factorBlockValue).prod) = 1050564897764164459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_fourteenL_144825599360927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1050564897764164459) ^ 525282448882082229 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050564897764164459) ^ 350188299254721486 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050564897764164459) ^ 80812684443397266 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050564897764164459) ^ 33889190250456918 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050564897764164459) ^ 7254 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1236495880396527397 : Nat.Prime 1236495880396527397 := by
  apply lucas_primality 1236495880396527397 (2 : ZMod 1236495880396527397)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3307, 1), (116443, 1), (267586283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3307, 1), (116443, 1), (267586283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1236495880396527397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_3307
      · exact prime_fourteenL_116443
      · exact prime_fourteenL_267586283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1236495880396527397) ^ 618247940198263698 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 412165293465509132 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 373902594616428 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 10618894054572 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 4620924012 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1533142745943043289 : Nat.Prime 1533142745943043289 := by
  apply lucas_primality 1533142745943043289 (3 : ZMod 1533142745943043289)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1533142745943043289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_157
      · exact prime_fourteenL_10211
      · exact prime_fourteenL_119543144893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1533142745943043289) ^ 766571372971521644 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 9765240420019384 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 150146189985608 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 12825016 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1570470015063981253 : Nat.Prime 1570470015063981253 := by
  apply lucas_primality 1570470015063981253 (5 : ZMod 1570470015063981253)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1570470015063981253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_89
      · exact prime_t64_1151
      · exact prime_fourteenL_3301
      · exact prime_fourteenL_2290081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1570470015063981253) ^ 785235007531990626 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 523490005021327084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 120805385774152404 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 17645730506336868 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 1364439630811452 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 475755836129652 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 685770509892 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_1816479359975242957 : Nat.Prime 1816479359975242957 := by
  apply lucas_primality 1816479359975242957 (2 : ZMod 1816479359975242957)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1747, 1), (16333, 1), (757865809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1747, 1), (16333, 1), (757865809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1816479359975242957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_fourteenL_1747
      · exact prime_fourteenL_16333
      · exact prime_fourteenL_757865809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1816479359975242957) ^ 908239679987621478 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1816479359975242957) ^ 605493119991747652 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1816479359975242957) ^ 259497051425034708 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1816479359975242957) ^ 1039770669705348 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1816479359975242957) ^ 111215291739132 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1816479359975242957) ^ 2396835084 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3357640771913012023 : Nat.Prime 3357640771913012023 := by
  apply lucas_primality 3357640771913012023 (5 : ZMod 3357640771913012023)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3357640771913012023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_439
      · exact prime_fourteenL_20549
      · exact prime_fourteenL_1088310731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3357640771913012023) ^ 1678820385956506011 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 1119213590637670674 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 176717935363842738 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 7648384446271098 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 163396796530878 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 3085185762 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7361524796742341989 : Nat.Prime 7361524796742341989 := by
  apply lucas_primality 7361524796742341989 (2 : ZMod 7361524796742341989)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod) = 7361524796742341989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_fourteenL_18223631
      · exact prime_fourteenL_90735599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7361524796742341989) ^ 3680762398371170994 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 2453841598914113996 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 1051646399534620284 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 138896694278157396 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 403954886748 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 81131605212 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_7510116500595532297 : Nat.Prime 7510116500595532297 := by
  apply lucas_primality 7510116500595532297 (5 : ZMod 7510116500595532297)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod) = 7510116500595532297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_fourteenL_443
      · exact prime_fourteenL_3457
      · exact prime_fourteenL_15683
      · exact prime_fourteenL_394811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7510116500595532297) ^ 3755058250297766148 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2503372166865177432 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 682737863690502936 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 16952858917822872 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2172437518251528 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 478869891002712 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 19022054858136 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_11891227458126031349 : Nat.Prime 11891227458126031349 := by
  apply lucas_primality 11891227458126031349 (2 : ZMod 11891227458126031349)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) = 11891227458126031349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_137
      · exact prime_fourteenL_25457
      · exact prime_fourteenL_852391097893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11891227458126031349) ^ 5945613729063015674 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 86797280716248404 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 467110321645364 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 13950436 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_14143091156502206219 : Nat.Prime 14143091156502206219 := by
  apply lucas_primality 14143091156502206219 (2 : ZMod 14143091156502206219)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) = 14143091156502206219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_419
      · exact prime_fourteenL_16877197084131511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14143091156502206219) ^ 7071545578251103109 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 33754394168263022 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 838 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_15713735765743224997 : Nat.Prime 15713735765743224997 := by
  apply lucas_primality 15713735765743224997 (2 : ZMod 15713735765743224997)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod) = 15713735765743224997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_fourteenL_2687
      · exact prime_fourteenL_1686291654781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15713735765743224997) ^ 7856867882871612498 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5237911921914408332 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 924337397984895588 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5848059458780508 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 9318516 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_53432285109967285069 : Nat.Prime 53432285109967285069 := by
  apply lucas_primality 53432285109967285069 (2 : ZMod 53432285109967285069)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (811821761, 1), (5484812849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (811821761, 1), (5484812849, 1)] : List FactorBlock).map factorBlockValue).prod) = 53432285109967285069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_811821761
      · exact prime_fourteenL_5484812849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53432285109967285069) ^ 26716142554983642534 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 17810761703322428356 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 65817754188 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 9741861132 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_78585209989176375449 : Nat.Prime 78585209989176375449 := by
  apply lucas_primality 78585209989176375449 (3 : ZMod 78585209989176375449)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (13505171, 1), (23463297631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (13505171, 1), (23463297631, 1)] : List FactorBlock).map factorBlockValue).prod) = 78585209989176375449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_fourteenL_13505171
      · exact prime_fourteenL_23463297631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 78585209989176375449) ^ 39292604994588187724 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 2535006773844399208 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 5818897812488 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 3349282408 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_139
      · exact prime_fourteenL_413869
      · exact prime_fourteenL_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_198003276191030887067 : Nat.Prime 198003276191030887067 := by
  apply lucas_primality 198003276191030887067 (2 : ZMod 198003276191030887067)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) = 198003276191030887067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_fourteenL_14143091156502206219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 198003276191030887067) ^ 99001638095515443533 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 28286182313004412438 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 14 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_361586454322254942197 : Nat.Prime 361586454322254942197 := by
  apply lucas_primality 361586454322254942197 (2 : ZMod 361586454322254942197)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) = 361586454322254942197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_71
      · exact prime_fourteenL_97937826197793863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361586454322254942197) ^ 180793227161127471098 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 27814342640173457092 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 5092766962285280876 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 3692 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_539990357450780531927 : Nat.Prime 539990357450780531927 := by
  apply lucas_primality 539990357450780531927 (5 : ZMod 539990357450780531927)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (1050564897764164459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (1050564897764164459, 1)] : List FactorBlock).map factorBlockValue).prod) = 539990357450780531927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_257
      · exact prime_fourteenL_1050564897764164459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 539990357450780531927) ^ 269995178725390265963 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 539990357450780531927) ^ 2101129795528328918 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 539990357450780531927) ^ 514 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_607348163015529886877 : Nat.Prime 607348163015529886877 := by
  apply lucas_primality 607348163015529886877 (2 : ZMod 607348163015529886877)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) = 607348163015529886877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_2837
      · exact prime_fourteenL_2633923
      · exact prime_fourteenL_20319607769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607348163015529886877) ^ 303674081507764943438 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 214081129014991148 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 230586908962612 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 29889758204 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_767070978526931087231 : Nat.Prime 767070978526931087231 := by
  apply lucas_primality 767070978526931087231 (38 : ZMod 767070978526931087231)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (37, 1), (6933661561302821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (37, 1), (6933661561302821, 1)] : List FactorBlock).map factorBlockValue).prod) = 767070978526931087231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_t64_37
      · exact prime_fourteenL_6933661561302821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 767070978526931087231) ^ 383535489263465543615 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 153414195705386217446 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 59005459886687006710 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 33350912109866569010 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 20731648068295434790 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 110630 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_841494022279382485723 : Nat.Prime 841494022279382485723 := by
  apply lucas_primality 841494022279382485723 (2 : ZMod 841494022279382485723)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4909, 1), (28569770566964843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4909, 1), (28569770566964843, 1)] : List FactorBlock).map factorBlockValue).prod) = 841494022279382485723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_4909
      · exact prime_fourteenL_28569770566964843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 841494022279382485723) ^ 420747011139691242861 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 280498007426460828574 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 171418623401789058 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 29454 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_927515741733830445223 : Nat.Prime 927515741733830445223 := by
  apply lucas_primality 927515741733830445223 (3 : ZMod 927515741733830445223)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) = 927515741733830445223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_fourteenL_11891227458126031349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 927515741733830445223) ^ 463757870866915222611 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 309171913911276815074 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 71347364748756188094 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 78 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_2745282942209897032861 : Nat.Prime 2745282942209897032861 := by
  apply lucas_primality 2745282942209897032861 (2 : ZMod 2745282942209897032861)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (29, 1), (251, 1), (20809, 1), (4794820817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (29, 1), (251, 1), (20809, 1), (4794820817, 1)] : List FactorBlock).map factorBlockValue).prod) = 2745282942209897032861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_t64_251
      · exact prime_fourteenL_20809
      · exact prime_fourteenL_4794820817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2745282942209897032861) ^ 1372641471104948516430 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 915094314069965677620 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 549056588441979406572 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 392183277458556718980 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 94664929041720587340 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 10937382239880067860 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 131927672747844540 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745282942209897032861) ^ 572551727580 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_3376719396603664660873 : Nat.Prime 3376719396603664660873 := by
  apply lucas_primality 3376719396603664660873 (15 : ZMod 3376719396603664660873)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3376719396603664660873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_2633
      · exact prime_fourteenL_659702079143411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 3376719396603664660873) ^ 1688359698301832330436 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1125573132201221553624 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1282460841854790984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 5118552 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_29
      · exact prime_t64_431
      · exact prime_fourteenL_3532679
      · exact prime_fourteenL_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_67
      · exact prime_fourteenL_19379
      · exact prime_fourteenL_311677
      · exact prime_fourteenL_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_14115836970606756764153 : Nat.Prime 14115836970606756764153 := by
  apply lucas_primality 14115836970606756764153 (3 : ZMod 14115836970606756764153)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1427, 1), (1236495880396527397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1427, 1), (1236495880396527397, 1)] : List FactorBlock).map factorBlockValue).prod) = 14115836970606756764153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_1427
      · exact prime_fourteenL_1236495880396527397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14115836970606756764153) ^ 7057918485303378382076 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14115836970606756764153) ^ 9891967043172219176 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14115836970606756764153) ^ 11416 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_fourteenL_6475879
      · exact prime_fourteenL_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_50626684582777451757247 : Nat.Prime 50626684582777451757247 := by
  apply lucas_primality 50626684582777451757247 (6 : ZMod 50626684582777451757247)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (767070978526931087231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (767070978526931087231, 1)] : List FactorBlock).map factorBlockValue).prod) = 50626684582777451757247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_fourteenL_767070978526931087231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 50626684582777451757247) ^ 25313342291388725878623 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 16875561527592483919082 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 4602425871161586523386 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 66 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_85012796177853340036873 : Nat.Prime 85012796177853340036873 := by
  apply lucas_primality 85012796177853340036873 (5 : ZMod 85012796177853340036873)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 2), (53, 1), (281, 1), (2909, 1), (282910655971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 2), (53, 1), (281, 1), (2909, 1), (282910655971, 1)] : List FactorBlock).map factorBlockValue).prod) = 85012796177853340036873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_53
      · exact prime_fourteenL_281
      · exact prime_t64_2909
      · exact prime_fourteenL_282910655971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85012796177853340036873) ^ 42506398088926670018436 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 28337598725951113345624 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 5000752716344314119816 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 1604015022223647925224 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 302536641202325053512 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 29224061938072650408 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85012796177853340036873) ^ 300493439832 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_270718619192664568942739 : Nat.Prime 270718619192664568942739 := by
  apply lucas_primality 270718619192664568942739 (2 : ZMod 270718619192664568942739)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod) = 270718619192664568942739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_23669
      · exact prime_fourteenL_1462090577
      · exact prime_fourteenL_3911415413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 270718619192664568942739) ^ 135359309596332284471369 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 11437687236159726602 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 185158582820594 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 69212443734026 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_291830251554904380435479 : Nat.Prime 291830251554904380435479 := by
  apply lucas_primality 291830251554904380435479 (13 : ZMod 291830251554904380435479)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17290739, 1), (8438917837893001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17290739, 1), (8438917837893001, 1)] : List FactorBlock).map factorBlockValue).prod) = 291830251554904380435479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_fourteenL_17290739
      · exact prime_fourteenL_8438917837893001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 291830251554904380435479) ^ 145915125777452190217739 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 291830251554904380435479) ^ 16877835675786002 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 291830251554904380435479) ^ 34581478 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_466758872492019732809539 : Nat.Prime 466758872492019732809539 := by
  apply lucas_primality 466758872492019732809539 (2 : ZMod 466758872492019732809539)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (9161, 1), (116325676917092891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (9161, 1), (116325676917092891, 1)] : List FactorBlock).map factorBlockValue).prod) = 466758872492019732809539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_fourteenL_9161
      · exact prime_fourteenL_116325676917092891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 466758872492019732809539) ^ 233379436246009866404769 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 466758872492019732809539) ^ 155586290830673244269846 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 466758872492019732809539) ^ 6393957157424927846706 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 466758872492019732809539) ^ 50950646489686686258 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (2 : ZMod 466758872492019732809539) ^ 4012518 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_239
      · exact prime_fourteenL_4519
      · exact prime_fourteenL_15661
      · exact prime_fourteenL_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_9858091946062842016175737 : Nat.Prime 9858091946062842016175737 := by
  apply lucas_primality 9858091946062842016175737 (10 : ZMod 9858091946062842016175737)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) = 9858091946062842016175737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_fourteenL_4703
      · exact prime_fourteenL_215497
      · exact prime_fourteenL_135096519595393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9858091946062842016175737) ^ 4929045973031421008087868 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 3286030648687614005391912 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 2096128417193885183112 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 45745843079313596088 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 72970732152 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_fourteenL_1173959
      · exact prime_fourteenL_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_991
      · exact prime_fourteenL_3779417
      · exact prime_fourteenL_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_179910178015646866795207201 : Nat.Prime 179910178015646866795207201 := by
  apply lucas_primality 179910178015646866795207201 (79 : ZMod 179910178015646866795207201)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 179910178015646866795207201 - 1 by
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
    · change (79 : ZMod 179910178015646866795207201) ^ 89955089007823433397603600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 59970059338548955598402400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 35982035603129373359041440 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 25701454002235266685029600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 16355470728695169708655200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 13839244462742066676554400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 10582951647979227458541600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 9468956737665624568168800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 6203799241918857475696800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 5803554129536995703071200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4862437243666131535005600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4388053122332850409639200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4183957628270857367330400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3827876127992486527557600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3394531660672582392362400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3049325051112658759240800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 2949347180584374865495200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_201850443627311118843403201 : Nat.Prime 201850443627311118843403201 := by
  apply lucas_primality 201850443627311118843403201 (41 : ZMod 201850443627311118843403201)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 201850443627311118843403201 - 1 by
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
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 201850443627311118843403201) ^ 100925221813655559421701600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 67283481209103706281134400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 40370088725462223768680640 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 28835777661044445549057600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 18350040329755556258491200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 15526957202100855295646400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 11873555507488889343729600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 10623707559332164149652800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 8776106244665700819278400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 6960360125079693753220800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 6511304633139068349787200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 5455417395332732941713600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 4694196363425839973102400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 4294690289942789762625600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3808498936364360732894400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3421193959784934217684800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3309023666021493751531200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_212201748428711689040500801 : Nat.Prime 212201748428711689040500801 := by
  apply lucas_primality 212201748428711689040500801 (13 : ZMod 212201748428711689040500801)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 3), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 3), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 212201748428711689040500801 - 1 by
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
    · change (13 : ZMod 212201748428711689040500801) ^ 106100874214355844520250400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 70733916142903896346833600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 42440349685742337808100160 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 30314535489815955577214400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 19291068038973789912772800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 12482455789924217002382400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 11168513075195352054763200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 9226162975161377784369600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 7317301669955575484155200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 6845217691248764162596800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 5735182389965180784878400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 5175652400700285098548800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4934924382063062535825600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4514930817632163596606400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4003806574126635642273600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 3596639803876469305771200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 3478717187355929328532800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_239880237354195822393609601 : Nat.Prime 239880237354195822393609601 := by
  apply lucas_primality 239880237354195822393609601 (71 : ZMod 239880237354195822393609601)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 239880237354195822393609601 - 1 by
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
    · change (71 : ZMod 239880237354195822393609601) ^ 119940118677097911196804800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 79960079118065274131203200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 47976047470839164478721920 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 34268605336313688913372800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 21807294304926892944873600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 18452325950322755568739200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 14110602197305636611388800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 12625275650220832757558400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 8271732322558476634262400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 7738072172715994270761600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 6483249658221508713340800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 5850737496443800546185600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 5578610171027809823107200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 5103834837323315370076800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 4526042214230109856483200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 4065766734816878345654400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (71 : ZMod 239880237354195822393609601) ^ 3932462907445833153993600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_280537904702364605850153601 : Nat.Prime 280537904702364605850153601 := by
  apply lucas_primality 280537904702364605850153601 (113 : ZMod 280537904702364605850153601)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 280537904702364605850153601 - 1 by
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
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 280537904702364605850153601) ^ 140268952351182302925076800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 93512634900788201950051200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 56107580940472921170030720 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 40076843528909229407164800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 25503445882033145986377600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 21579838823258815834627200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 16502229688374388579420800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 14765152879071821360534400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 12197300204450635036963200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 9673720851805676063798400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 9049609829108535672585600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 7582105532496340698652800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 6842387919569868435369600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 6524137318659641996515200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 5968891589412012890428800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 5293168013252162374531200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 280537904702364605850153601) ^ 4598982044301059112297600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_285374765128267443882052801 : Nat.Prime 285374765128267443882052801 := by
  apply lucas_primality 285374765128267443882052801 (29 : ZMod 285374765128267443882052801)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 285374765128267443882052801 - 1 by
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
    · change (29 : ZMod 285374765128267443882052801) ^ 142687382564133721941026400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 95124921709422481294017600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 57074953025653488776410560 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 40767823589752491983150400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 25943160466206131262004800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 21951905009866726452465600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 16786750889898084934238400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 15019724480435128625371200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 12407598483837714951393600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 9205637584782820770388800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 7712831489953174158974400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6960360125079693753220800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6636622444843428927489600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6071803513367392423022400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 5384429530722027243057600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4836860425902838031899200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4678274838168318752164800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_331034727548790234903181249 : Nat.Prime 331034727548790234903181249 := by
  apply lucas_primality 331034727548790234903181249 (67 : ZMod 331034727548790234903181249)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 331034727548790234903181249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
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
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 331034727548790234903181249) ^ 165517363774395117451590624 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 110344909182930078301060416 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 47290675364112890700454464 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 30094066140799112263925568 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 25464209811445402684860096 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 19472631032281778523716544 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 17422880397304749205430592 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 14392814241251749343616576 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 11414990605130697755282112 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 10678539598348072093651008 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8946884528345682024410304 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8074017745092444753736128 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7698482036018377555887936 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7043292075506175210705984 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 6245938255637551601946816 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5610758094047292117003072 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5426798812275249752511168 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_344827841196656494690813801 : Nat.Prime 344827841196656494690813801 := by
  apply lucas_primality 344827841196656494690813801 (97 : ZMod 344827841196656494690813801)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 344827841196656494690813801 - 1 by
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
    · change (97 : ZMod 344827841196656494690813801) ^ 172413920598328247345406900 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 114942613732218831563604600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 68965568239331298938162760 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 49261120170950927812973400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 31347985563332408608255800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 26525218553588961130062600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 20283990658626852628871400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 18148833747192447088990200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 14992514834637238899600600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11890615213677810161752200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11123478748279241764219800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 9319671383693418775427400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8410435151137963285141800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8019252120852476620716600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 7336762578652265844485400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 6506185682955782918694600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5844539681299262621878200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5652915429453385158865800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_376175826759988903299069601 : Nat.Prime 376175826759988903299069601 := by
  apply lucas_primality 376175826759988903299069601 (33 : ZMod 376175826759988903299069601)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 376175826759988903299069601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
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
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 376175826759988903299069601) ^ 188087913379994451649534800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 125391942253329634433023200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 75235165351997780659813920 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 53739403822855557614152800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 28936602058460684869159200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 22127989809411111958768800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 19798727724209942278898400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 16355470728695169708655200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12971580233103065631002400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12134704089031900106421600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 10166914236756456845920800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 9175020164877778129245600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8748275040929974495327200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8003740994893380921256800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 7097657108679035911303200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6375861470508286496594400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6166816832130965627853600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
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
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem prime_fourteenL_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← fourteenLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 919540909857750652508836801 - 1 by
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
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← fourteenLFastPow_eq_pow]
      decide

private theorem phi_fourteenL_16551736377439511745159062400 : Nat.totient 16551736377439511745159062400 = 2177999158431048951398400000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062401 : Nat.totient 16551736377439511745159062401 = 16487838943942525052785605120 := by
  rw [← show ((([(269, 1), (7691, 1), (111869, 1), (218857, 1), (326767060643, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_269, prime_fourteenL_7691, prime_fourteenL_111869, prime_fourteenL_218857, prime_fourteenL_326767060643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062402 : Nat.totient 16551736377439511745159062402 = 8275803273330824297157026692 := by
  rw [← show ((([(2, 1), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_fourteenL_127487, prime_fourteenL_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062403 : Nat.totient 16551736377439511745159062403 = 10966794654856099114012645440 := by
  rw [← show ((([(3, 1), (163, 1), (81554969011, 1), (415034571917257, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_163, prime_fourteenL_81554969011, prime_fourteenL_415034571917257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062404 : Nat.totient 16551736377439511745159062404 = 8275845428494711196383989800 := by
  rw [← show ((([(2, 2), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_fourteenL_363611, prime_fourteenL_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062405 : Nat.totient 16551736377439511745159062405 = 13227264892236486626093133120 := by
  rw [← show ((([(5, 1), (1667, 1), (2141, 1), (927515741733830445223, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_fourteenL_1667, prime_fourteenL_2141, prime_fourteenL_927515741733830445223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062406 : Nat.totient 16551736377439511745159062406 = 5476973594481200966767961984 := by
  rw [← show ((([(2, 1), (3, 1), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_137, prime_fourteenL_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062407 : Nat.totient 16551736377439511745159062407 = 14187135113158311726045645312 := by
  rw [← show ((([(7, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062408 : Nat.totient 16551736377439511745159062408 = 8271998644469182032865992768 := by
  rw [← show ((([(2, 3), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_fourteenL_3023, prime_fourteenL_7309, prime_fourteenL_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062409 : Nat.totient 16551736377439511745159062409 = 10978476427164975651883134720 := by
  rw [← show ((([(3, 2), (197, 1), (5944361, 1), (1570470015063981253, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_197, prime_fourteenL_5944361, prime_fourteenL_1570470015063981253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062410 : Nat.totient 16551736377439511745159062410 = 6546304724560346218310100736 := by
  rw [← show ((([(2, 1), (5, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_89, prime_fourteenL_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062411 : Nat.totient 16551736377439511745159062411 = 15020085351868930137738700800 := by
  rw [← show ((([(11, 1), (643, 1), (4289, 1), (344543, 1), (1583581521533941, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_fourteenL_643, prime_fourteenL_4289, prime_fourteenL_344543, prime_fourteenL_1583581521533941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062412 : Nat.totient 16551736377439511745159062412 = 5496075831709035835541959680 := by
  rw [← show ((([(2, 2), (3, 1), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_263, prime_fourteenL_33811, prime_fourteenL_189853, prime_fourteenL_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062413 : Nat.totient 16551736377439511745159062413 = 15278525886866354752650863664 := by
  rw [← show ((([(13, 1), (27346626158783, 1), (46558229274047, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_fourteenL_27346626158783, prime_fourteenL_46558229274047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062414 : Nat.totient 16551736377439511745159062414 = 7023328967119773837005857152 := by
  rw [← show ((([(2, 1), (7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062415 : Nat.totient 16551736377439511745159062415 = 8827591150608196735793153696 := by
  rw [← show ((([(3, 1), (5, 1), (5572883, 1), (198003276191030887067, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_fourteenL_5572883, prime_fourteenL_198003276191030887067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062416 : Nat.totient 16551736377439511745159062416 = 8232988042664213096037666816 := by
  rw [← show ((([(2, 4), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_193, prime_fourteenL_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062417 : Nat.totient 16551736377439511745159062417 = 15576074152088802025107456000 := by
  rw [← show ((([(17, 1), (7681, 1), (6135331, 1), (20660407174714891, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_fourteenL_7681, prime_fourteenL_6135331, prime_fourteenL_20660407174714891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062418 : Nat.totient 16551736377439511745159062418 = 5517245459146503915053020800 := by
  rw [← show ((([(2, 1), (3, 2), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_fourteenL_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062419 : Nat.totient 16551736377439511745159062419 = 15667427900794711599210931200 := by
  rw [← show ((([(19, 1), (1201, 1), (201823, 1), (512903, 1), (7007144209529, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_fourteenL_1201, prime_fourteenL_201823, prime_fourteenL_512903, prime_fourteenL_7007144209529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062420 : Nat.totient 16551736377439511745159062420 = 6552316620150743707747430400 := by
  rw [← show ((([(2, 2), (5, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_97, prime_fourteenL_72973, prime_fourteenL_195271, prime_fourteenL_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062421 : Nat.totient 16551736377439511745159062421 = 9429298375565393472865536000 := by
  rw [← show ((([(3, 1), (7, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062422 : Nat.totient 16551736377439511745159062422 = 7523516535199778065981392000 := by
  rw [← show ((([(2, 1), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_fourteenL_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062423 : Nat.totient 16551736377439511745159062423 = 15615217642563541753622365824 := by
  rw [← show ((([(23, 1), (73, 1), (9858091946062842016175737, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_73, prime_fourteenL_9858091946062842016175737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062424 : Nat.totient 16551736377439511745159062424 = 5451630663625874187347763200 := by
  rw [← show ((([(2, 3), (3, 1), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_fourteenL_131, prime_t64_233, prime_fourteenL_550990241, prime_fourteenL_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062425 : Nat.totient 16551736377439511745159062425 = 13241077268160144507113903040 := by
  rw [← show ((([(5, 2), (42463, 1), (102310987907, 1), (152394958517, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_fourteenL_42463, prime_fourteenL_102310987907, prime_fourteenL_152394958517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062426 : Nat.totient 16551736377439511745159062426 = 7638527762705737673822738640 := by
  rw [← show ((([(2, 1), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_fourteenL_10391, prime_fourteenL_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062427 : Nat.totient 16551736377439511745159062427 = 11033316098868550709001686400 := by
  rw [← show ((([(3, 4), (10141, 1), (127241, 1), (158361893331124207, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_fourteenL_10141, prime_fourteenL_127241, prime_fourteenL_158361893331124207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062428 : Nat.totient 16551736377439511745159062428 = 7093601298814946944586473200 := by
  rw [← show ((([(2, 2), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062429 : Nat.totient 16551736377439511745159062429 = 15980986753169035239071032176 := by
  rw [← show ((([(29, 1), (169985287, 1), (3357640771913012023, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_fourteenL_169985287, prime_fourteenL_3357640771913012023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062430 : Nat.totient 16551736377439511745159062430 = 4413796367140036680980727456 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_fourteenL_24913302187, prime_fourteenL_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062431 : Nat.totient 16551736377439511745159062431 = 15890611991860846144983859200 := by
  rw [← show ((([(31, 1), (139, 1), (1381, 1), (35747, 1), (10167809, 1), (7652554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_t64_139, prime_fourteenL_1381, prime_fourteenL_35747, prime_fourteenL_10167809, prime_fourteenL_7652554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062432 : Nat.totient 16551736377439511745159062432 = 8169798577282448507783036928 := by
  rw [← show ((([(2, 5), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_79, prime_fourteenL_6229, prime_fourteenL_8696692033, prime_fourteenL_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062433 : Nat.totient 16551736377439511745159062433 = 10031287845878438681345667840 := by
  rw [← show ((([(3, 1), (11, 1), (148537, 1), (3376719396603664660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_fourteenL_148537, prime_fourteenL_3376719396603664660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062434 : Nat.totient 16551736377439511745159062434 = 7789046627529442253386001152 := by
  rw [← show ((([(2, 1), (17, 1), (1346333, 1), (361586454322254942197, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_fourteenL_1346333, prime_fourteenL_361586454322254942197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062435 : Nat.totient 16551736377439511745159062435 = 11299652204252097710385228672 := by
  rw [← show ((([(5, 1), (7, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062436 : Nat.totient 16551736377439511745159062436 = 5502865884038948229442260480 := by
  rw [← show ((([(2, 2), (3, 2), (521, 1), (1453, 1), (607348163015529886877, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_521, prime_fourteenL_1453, prime_fourteenL_607348163015529886877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062437 : Nat.totient 16551736377439511745159062437 = 16091987193044236941433242624 := by
  rw [← show ((([(37, 1), (2063, 1), (3539, 1), (360037, 1), (3015373, 1), (56438293, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_fourteenL_2063, prime_fourteenL_3539, prime_fourteenL_360037, prime_fourteenL_3015373, prime_fourteenL_56438293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062438 : Nat.totient 16551736377439511745159062438 = 7840296176731207853368336200 := by
  rw [← show ((([(2, 1), (19, 1), (3813504911, 1), (114218290024018991, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_fourteenL_3813504911, prime_fourteenL_114218290024018991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062439 : Nat.totient 16551736377439511745159062439 = 9963331525890602505826012800 := by
  rw [← show ((([(3, 1), (13, 1), (83, 1), (101, 1), (50626684582777451757247, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_t64_83, prime_t64_101, prime_fourteenL_50626684582777451757247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062440 : Nat.totient 16551736377439511745159062440 = 6609998760007932994254531072 := by
  rw [← show ((([(2, 3), (5, 1), (619, 1), (70908014633, 1), (9427522870043, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_fourteenL_619, prime_fourteenL_70908014633, prime_fourteenL_9427522870043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062441 : Nat.totient 16551736377439511745159062441 = 16043089186760802569167564800 := by
  rw [← show ((([(41, 1), (157, 1), (7993, 1), (239069, 1), (888691, 1), (1514175419, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_157, prime_fourteenL_7993, prime_fourteenL_239069, prime_fourteenL_888691, prime_fourteenL_1514175419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062442 : Nat.totient 16551736377439511745159062442 = 4729067536411289070045446400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062443 : Nat.totient 16551736377439511745159062443 = 16154555405073286883386320168 := by
  rw [← show ((([(43, 1), (1319, 1), (291830251554904380435479, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_fourteenL_1319, prime_fourteenL_291830251554904380435479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062444 : Nat.totient 16551736377439511745159062444 = 7523516535199778065981392000 := by
  rw [← show ((([(2, 2), (11, 1), (376175826759988903299069601, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_fourteenL_376175826759988903299069601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062445 : Nat.totient 16551736377439511745159062445 = 8679545836486682599141781760 := by
  rw [← show ((([(3, 2), (5, 1), (71, 1), (367, 1), (14115836970606756764153, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_71, prime_fourteenL_367, prime_fourteenL_14115836970606756764153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062446 : Nat.totient 16551736377439511745159062446 = 7912878563756018218325799840 := by
  rw [← show ((([(2, 1), (23, 1), (2939, 1), (16631, 1), (7361524796742341989, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_fourteenL_2939, prime_fourteenL_16631, prime_fourteenL_7361524796742341989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062447 : Nat.totient 16551736377439511745159062447 = 16199571772684746867371444352 := by
  rw [← show ((([(47, 1), (16539367177, 1), (21292507748726713, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_fourteenL_16539367177, prime_fourteenL_21292507748726713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062448 : Nat.totient 16551736377439511745159062448 = 5517245459146503915053020800 := by
  rw [← show ((([(2, 4), (3, 1), (344827841196656494690813801, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_fourteenL_344827841196656494690813801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062449 : Nat.totient 16551736377439511745159062449 = 14187057133780802457538392264 := by
  rw [← show ((([(7, 2), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062450 : Nat.totient 16551736377439511745159062450 = 6620694550975804698063624960 := by
  rw [← show ((([(2, 1), (5, 2), (331034727548790234903181249, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_fourteenL_331034727548790234903181249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062451 : Nat.totient 16551736377439511745159062451 = 10385323554833964858306425856 := by
  rw [← show ((([(3, 1), (17, 1), (130439, 1), (238569407, 1), (10429204246537, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_fourteenL_130439, prime_fourteenL_238569407, prime_fourteenL_10429204246537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062452 : Nat.totient 16551736377439511745159062452 = 7639250559633289310005531008 := by
  rw [← show ((([(2, 2), (13, 1), (620159, 1), (116512763, 1), (4405180062253, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_fourteenL_620159, prime_fourteenL_116512763, prime_fourteenL_4405180062253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062453 : Nat.totient 16551736377439511745159062453 = 16239264809890086491617668864 := by
  rw [← show ((([(53, 1), (93179, 1), (43585393, 1), (76896872970083, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_fourteenL_93179, prime_fourteenL_43585393, prime_fourteenL_76896872970083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062454 : Nat.totient 16551736377439511745159062454 = 5499798181795815391554280704 := by
  rw [← show ((([(2, 1), (3, 3), (317, 1), (128749, 1), (7510116500595532297, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_317, prime_fourteenL_128749, prime_fourteenL_7510116500595532297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062455 : Nat.totient 16551736377439511745159062455 = 12037516645001956509684528000 := by
  rw [← show ((([(5, 1), (11, 1), (109621, 1), (2745282942209897032861, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_fourteenL_109621, prime_fourteenL_2745282942209897032861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062456 : Nat.totient 16551736377439511745159062456 = 7093600965708594895951147008 := by
  rw [← show ((([(2, 3), (7, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062457 : Nat.totient 16551736377439511745159062457 = 10449274157033836870996637760 := by
  rw [← show ((([(3, 1), (19, 1), (2347, 1), (36033175631, 1), (3433626695693, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_fourteenL_2347, prime_fourteenL_36033175631, prime_fourteenL_3433626695693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062458 : Nat.totient 16551736377439511745159062458 = 7990493423591488428697478400 := by
  rw [← show ((([(2, 1), (29, 1), (285374765128267443882052801, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_fourteenL_285374765128267443882052801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062459 : Nat.totient 16551736377439511745159062459 = 16271198472737147139308908800 := by
  rw [← show ((([(59, 1), (280537904702364605850153601, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_fourteenL_280537904702364605850153601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062460 : Nat.totient 16551736377439511745159062460 = 4409464869410120498939316544 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1019, 1), (270718619192664568942739, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_fourteenL_1019, prime_fourteenL_270718619192664568942739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062461 : Nat.totient 16551736377439511745159062461 = 16280057381453525561705902080 := by
  rw [← show ((([(61, 1), (48017, 1), (39181973737, 1), (144222292169, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_fourteenL_48017, prime_fourteenL_39181973737, prime_fourteenL_144222292169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062462 : Nat.totient 16551736377439511745159062462 = 7973915489449094086047129600 := by
  rw [← show ((([(2, 1), (31, 1), (257, 1), (2099, 1), (319919, 1), (20354891, 1), (75997183, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_fourteenL_257, prime_fourteenL_2099, prime_fourteenL_319919, prime_fourteenL_20354891, prime_fourteenL_75997183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062463 : Nat.totient 16551736377439511745159062463 = 9289228977882265358296627200 := by
  rw [← show ((([(3, 2), (7, 1), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_67, prime_t64_491, prime_t64_1061, prime_t64_9492089, prime_lucas_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062464 : Nat.totient 16551736377439511745159062464 = 8274160930018441564353423360 := by
  rw [← show ((([(2, 6), (5821, 1), (28979, 1), (1533142745943043289, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_fourteenL_5821, prime_fourteenL_28979, prime_fourteenL_1533142745943043289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062465 : Nat.totient 16551736377439511745159062465 = 12222808639221092123423913984 := by
  rw [← show ((([(5, 1), (13, 1), (1014907, 1), (453380897, 1), (553402018259, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_fourteenL_1014907, prime_fourteenL_453380897, prime_fourteenL_553402018259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062466 : Nat.totient 16551736377439511745159062466 = 5015677375858470062137237440 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (15959533, 1), (15713735765743224997, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_fourteenL_15959533, prime_fourteenL_15713735765743224997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062467 : Nat.totient 16551736377439511745159062467 = 16509157075394901907537136512 := by
  rw [← show ((([(389, 1), (596093, 1), (7658927, 1), (9319916197373, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fourteenL_389, prime_fourteenL_596093, prime_fourteenL_7658927, prime_fourteenL_9319916197373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062468 : Nat.totient 16551736377439511745159062468 = 7753115812882953018094387200 := by
  rw [← show ((([(2, 2), (17, 1), (241, 1), (2153, 1), (548897, 1), (854639021934121, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_fourteenL_241, prime_fourteenL_2153, prime_fourteenL_548897, prime_fourteenL_854639021934121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062469 : Nat.totient 16551736377439511745159062469 = 10554730443584616185318822400 := by
  rw [← show ((([(3, 1), (23, 1), (239880237354195822393609601, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_fourteenL_239880237354195822393609601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062470 : Nat.totient 16551736377439511745159062470 = 5674881034629409990943511648 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062471 : Nat.totient 16551736377439511745159062471 = 16397036973971504083131312480 := by
  rw [← show ((([(107, 1), (2740211, 1), (3818077, 1), (14785332476099, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_107, prime_fourteenL_2740211, prime_fourteenL_3818077, prime_fourteenL_14785332476099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062472 : Nat.totient 16551736377439511745159062472 = 5517225263289969209866807008 := by
  rw [← show ((([(2, 3), (3, 2), (273187, 1), (841494022279382485723, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_fourteenL_273187, prime_fourteenL_841494022279382485723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062473 : Nat.totient 16551736377439511745159062473 = 16452624161936389488303097920 := by
  rw [← show ((([(167, 1), (760771409, 1), (130278547148823391, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_167, prime_fourteenL_760771409, prime_fourteenL_130278547148823391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062474 : Nat.totient 16551736377439511745159062474 = 8052163749580099852848112128 := by
  rw [← show ((([(2, 1), (37, 1), (307817, 1), (1305709, 1), (556509832673117, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_fourteenL_307817, prime_fourteenL_1305709, prime_fourteenL_556509832673117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062475 : Nat.totient 16551736377439511745159062475 = 8776433672836217119016870400 := by
  rw [← show ((([(3, 1), (5, 2), (173, 1), (66239, 1), (567315271, 1), (33946730509, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_fourteenL_173, prime_fourteenL_66239, prime_fourteenL_567315271, prime_fourteenL_33946730509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062476 : Nat.totient 16551736377439511745159062476 = 7840296173817616958879116032 := by
  rw [← show ((([(2, 2), (19, 1), (1577676713, 1), (138042225743563577, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_fourteenL_1577676713, prime_fourteenL_138042225743563577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062477 : Nat.totient 16551736377439511745159062477 = 12897456917485333827396672000 := by
  rw [← show ((([(7, 1), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_lucas_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062478 : Nat.totient 16551736377439511745159062478 = 5092841962289080536972019200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (212201748428711689040500801, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_fourteenL_212201748428711689040500801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062479 : Nat.totient 16551736377439511745159062479 = 16551269618567019725426217480 := by
  rw [← show ((([(35461, 1), (466758872492019732809539, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fourteenL_35461, prime_fourteenL_466758872492019732809539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062480 : Nat.totient 16551736377439511745159062480 = 6611960905078447592317587456 := by
  rw [← show ((([(2, 4), (5, 1), (1117, 1), (2357, 1), (78585209989176375449, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_fourteenL_1117, prime_fourteenL_2357, prime_fourteenL_78585209989176375449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062481 : Nat.totient 16551736377439511745159062481 = 11032960687961806469985248160 := by
  rw [← show ((([(3, 3), (7211, 1), (85012796177853340036873, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_fourteenL_7211, prime_fourteenL_85012796177853340036873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062482 : Nat.totient 16551736377439511745159062482 = 8074017745092444753736128000 := by
  rw [← show ((([(2, 1), (41, 1), (201850443627311118843403201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_fourteenL_201850443627311118843403201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062483 : Nat.totient 16551736377439511745159062483 = 16548387857013003123272813064 := by
  rw [← show ((([(4943, 1), (1534406528407, 1), (2182290251083, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fourteenL_4943, prime_fourteenL_1534406528407, prime_fourteenL_2182290251083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062484 : Nat.totient 16551736377439511745159062484 = 4717400485682981134329322752 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062485 : Nat.totient 16551736377439511745159062485 = 12461501695878194829233295360 := by
  rw [← show ((([(5, 1), (17, 1), (12689, 1), (771140911, 1), (19900477325279, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_fourteenL_12689, prime_fourteenL_771140911, prime_fourteenL_19900477325279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062486 : Nat.totient 16551736377439511745159062486 = 8079655789860152849537709600 := by
  rw [← show ((([(2, 1), (43, 1), (2179, 1), (222163, 1), (1881863, 1), (211265287151, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_fourteenL_2179, prime_fourteenL_222163, prime_fourteenL_1881863, prime_fourteenL_211265287151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062487 : Nat.totient 16551736377439511745159062487 = 10629271903332995308239195520 := by
  rw [← show ((([(3, 1), (29, 2), (431, 1), (116899877, 1), (130207195769087, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_431, prime_fourteenL_116899877, prime_fourteenL_130207195769087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062488 : Nat.totient 16551736377439511745159062488 = 7507747087159405068199526400 := by
  rw [← show ((([(2, 3), (11, 1), (479, 1), (242633, 1), (302287, 1), (1588921, 1), (3369409, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_479, prime_fourteenL_242633, prime_fourteenL_302287, prime_fourteenL_1588921, prime_fourteenL_3369409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062489 : Nat.totient 16551736377439511745159062489 = 16540234116553097765400236976 := by
  rw [← show ((([(1439, 1), (1396950757, 1), (8233825701109243, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fourteenL_1439, prime_fourteenL_1396950757, prime_fourteenL_8233825701109243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062490 : Nat.totient 16551736377439511745159062490 = 4409644159858699940223696768 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1063, 1), (29245518173, 1), (5915731660739, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_fourteenL_1063, prime_fourteenL_29245518173, prime_fourteenL_5915731660739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062491 : Nat.totient 16551736377439511745159062491 = 13095879331597461464761829664 := by
  rw [← show ((([(7, 1), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_lucas_4887540332063, prime_lucas_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062492 : Nat.totient 16551736377439511745159062492 = 7916047832688462138989116800 := by
  rw [← show ((([(2, 2), (23, 1), (179910178015646866795207201, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_fourteenL_179910178015646866795207201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062493 : Nat.totient 16551736377439511745159062493 = 10678075754597097848473651200 := by
  rw [← show ((([(3, 1), (31, 1), (23339, 1), (1694081, 1), (4501364654091139, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_fourteenL_23339, prime_fourteenL_1694081, prime_fourteenL_4501364654091139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062494 : Nat.totient 16551736377439511745159062494 = 8088840924414746013421532928 := by
  rw [← show ((([(2, 1), (47, 1), (937, 1), (3517, 1), (53432285109967285069, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_fourteenL_937, prime_fourteenL_3517, prime_fourteenL_53432285109967285069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062495 : Nat.totient 16551736377439511745159062495 = 12461378282081938182280809600 := by
  rw [← show ((([(5, 1), (19, 1), (151, 1), (635203, 1), (1816479359975242957, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_fourteenL_151, prime_fourteenL_635203, prime_fourteenL_1816479359975242957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062496 : Nat.totient 16551736377439511745159062496 = 5441666754200303387278162944 := by
  rw [← show ((([(2, 5), (3, 1), (73, 1), (210091982543, 1), (11241906997859, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_73, prime_fourteenL_210091982543, prime_fourteenL_11241906997859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062497 : Nat.totient 16551736377439511745159062497 = 16544129533274102599775169024 := by
  rw [← show ((([(2689, 1), (11399, 1), (539990357450780531927, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fourteenL_2689, prime_fourteenL_11399, prime_fourteenL_539990357450780531927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fourteenL_16551736377439511745159062498 : Nat.totient 16551736377439511745159062498 = 7078213882607007945748436640 := by
  rw [← show ((([(2, 1), (7, 2), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 16551736377439511745159062498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FourteenL : certifiedKill 1 16551736377439511745159062399 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fourteenL_16551736377439511745159062400, phi_fourteenL_16551736377439511745159062401, phi_fourteenL_16551736377439511745159062402,
    phi_fourteenL_16551736377439511745159062403, phi_fourteenL_16551736377439511745159062404, phi_fourteenL_16551736377439511745159062405,
    phi_fourteenL_16551736377439511745159062406, phi_fourteenL_16551736377439511745159062407, phi_fourteenL_16551736377439511745159062408,
    phi_fourteenL_16551736377439511745159062409, phi_fourteenL_16551736377439511745159062410, phi_fourteenL_16551736377439511745159062411,
    phi_fourteenL_16551736377439511745159062412, phi_fourteenL_16551736377439511745159062413, phi_fourteenL_16551736377439511745159062414,
    phi_fourteenL_16551736377439511745159062415, phi_fourteenL_16551736377439511745159062416, phi_fourteenL_16551736377439511745159062417,
    phi_fourteenL_16551736377439511745159062418, phi_fourteenL_16551736377439511745159062419, phi_fourteenL_16551736377439511745159062420,
    phi_fourteenL_16551736377439511745159062421, phi_fourteenL_16551736377439511745159062422, phi_fourteenL_16551736377439511745159062423,
    phi_fourteenL_16551736377439511745159062424, phi_fourteenL_16551736377439511745159062425, phi_fourteenL_16551736377439511745159062426,
    phi_fourteenL_16551736377439511745159062427, phi_fourteenL_16551736377439511745159062428, phi_fourteenL_16551736377439511745159062429,
    phi_fourteenL_16551736377439511745159062430, phi_fourteenL_16551736377439511745159062431, phi_fourteenL_16551736377439511745159062432,
    phi_fourteenL_16551736377439511745159062433, phi_fourteenL_16551736377439511745159062434, phi_fourteenL_16551736377439511745159062435,
    phi_fourteenL_16551736377439511745159062436, phi_fourteenL_16551736377439511745159062437, phi_fourteenL_16551736377439511745159062438,
    phi_fourteenL_16551736377439511745159062439, phi_fourteenL_16551736377439511745159062440, phi_fourteenL_16551736377439511745159062441,
    phi_fourteenL_16551736377439511745159062442, phi_fourteenL_16551736377439511745159062443, phi_fourteenL_16551736377439511745159062444,
    phi_fourteenL_16551736377439511745159062445, phi_fourteenL_16551736377439511745159062446, phi_fourteenL_16551736377439511745159062447,
    phi_fourteenL_16551736377439511745159062448, phi_fourteenL_16551736377439511745159062449, phi_fourteenL_16551736377439511745159062450,
    phi_fourteenL_16551736377439511745159062451, phi_fourteenL_16551736377439511745159062452, phi_fourteenL_16551736377439511745159062453,
    phi_fourteenL_16551736377439511745159062454, phi_fourteenL_16551736377439511745159062455, phi_fourteenL_16551736377439511745159062456,
    phi_fourteenL_16551736377439511745159062457, phi_fourteenL_16551736377439511745159062458, phi_fourteenL_16551736377439511745159062459,
    phi_fourteenL_16551736377439511745159062460, phi_fourteenL_16551736377439511745159062461, phi_fourteenL_16551736377439511745159062462,
    phi_fourteenL_16551736377439511745159062463, phi_fourteenL_16551736377439511745159062464, phi_fourteenL_16551736377439511745159062465,
    phi_fourteenL_16551736377439511745159062466, phi_fourteenL_16551736377439511745159062467, phi_fourteenL_16551736377439511745159062468,
    phi_fourteenL_16551736377439511745159062469, phi_fourteenL_16551736377439511745159062470, phi_fourteenL_16551736377439511745159062471,
    phi_fourteenL_16551736377439511745159062472, phi_fourteenL_16551736377439511745159062473, phi_fourteenL_16551736377439511745159062474,
    phi_fourteenL_16551736377439511745159062475, phi_fourteenL_16551736377439511745159062476, phi_fourteenL_16551736377439511745159062477,
    phi_fourteenL_16551736377439511745159062478, phi_fourteenL_16551736377439511745159062479, phi_fourteenL_16551736377439511745159062480,
    phi_fourteenL_16551736377439511745159062481, phi_fourteenL_16551736377439511745159062482, phi_fourteenL_16551736377439511745159062483,
    phi_fourteenL_16551736377439511745159062484, phi_fourteenL_16551736377439511745159062485, phi_fourteenL_16551736377439511745159062486,
    phi_fourteenL_16551736377439511745159062487, phi_fourteenL_16551736377439511745159062488, phi_fourteenL_16551736377439511745159062489,
    phi_fourteenL_16551736377439511745159062490, phi_fourteenL_16551736377439511745159062491, phi_fourteenL_16551736377439511745159062492,
    phi_fourteenL_16551736377439511745159062493, phi_fourteenL_16551736377439511745159062494, phi_fourteenL_16551736377439511745159062495,
    phi_fourteenL_16551736377439511745159062496, phi_fourteenL_16551736377439511745159062497, phi_fourteenL_16551736377439511745159062498]

end TotientTailPeriodKiller
end Erdos249257
